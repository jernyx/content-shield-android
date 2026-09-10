package com.example.contentshield

import android.accessibilityservice.AccessibilityService
import android.app.admin.DevicePolicyManager
import android.content.ComponentName
import android.content.Context
import android.view.accessibility.AccessibilityEvent
import android.util.Log

class BlockerAccessibilityService : AccessibilityService() {

    private lateinit var dpm: DevicePolicyManager
    private lateinit var adminComponent: ComponentName
    private var lastHandledPackage: String? = null

    private val settingsPackages = setOf(
        "com.android.settings",
        "com.samsung.android.settings",
        "com.miui.securitycenter"
    )

    // Anchor text unique to the "Reset" screen on your device (heading + first list item).
    private val resetScreenAnchors = listOf(
        "Reset all settings",
        "Reset accessibility settings"
    )

    // Maps browser package names to their URL bar view IDs.
    // Fallback: scan all nodes for text starting with "http" or a known domain pattern.
    private val browserUrlBarIds = mapOf(
        "com.android.chrome"            to "com.android.chrome:id/url_bar",
        "com.chrome.beta"               to "com.chrome.beta:id/url_bar",
        "com.chrome.dev"                to "com.chrome.dev:id/url_bar",
        "com.chrome.canary"             to "com.chrome.canary:id/url_bar",
        "org.mozilla.firefox"           to "org.mozilla.firefox:id/mozac_browser_toolbar_url_view",
        "org.mozilla.firefox_beta"      to "org.mozilla.firefox_beta:id/mozac_browser_toolbar_url_view",
        "org.mozilla.fenix"             to "org.mozilla.fenix:id/mozac_browser_toolbar_url_view",
        "com.microsoft.emmx"            to "com.microsoft.emmx:id/url_bar",          // Edge
        "com.opera.browser"             to "com.opera.browser:id/url_field",
        "com.opera.mini.native"         to "com.opera.mini.native:id/url_field",
        "com.brave.browser"             to "com.brave.browser:id/url_bar",
        "com.duckduckgo.mobile.android" to "com.duckduckgo.mobile.android:id/omnibarTextInput",
        "com.sec.android.app.sbrowser"  to "com.sec.android.app.sbrowser:id/location_bar_edit_text", // Samsung
        "com.UCMobile.intl"             to "com.UCMobile.intl:id/webview_tab_url",    // UC Browser
        "com.kiwibrowser.browser"       to "com.kiwibrowser.browser:id/url_bar"
    )

    override fun onServiceConnected() {
        super.onServiceConnected()
        dpm = getSystemService(Context.DEVICE_POLICY_SERVICE) as DevicePolicyManager
        adminComponent = ComponentName(this, MyDeviceAdminReceiver::class.java)
    }

    private fun getServiceDisplayLabel(): String {
        return try {
            val appInfo = packageManager.getApplicationInfo(packageName, 0)
            packageManager.getApplicationLabel(appInfo).toString()
        } catch (e: Exception) {
            "Content Shield"
        }
    }

    private fun screenContainsSwitch(rootNode: android.view.accessibility.AccessibilityNodeInfo): Boolean {
        val switchNodes = rootNode.findAccessibilityNodeInfosByViewId("android:id/switch_widget")
        if (switchNodes.isNotEmpty()) {
            switchNodes.forEach { it.recycle() }
            return true
        }
        return hasSwitchClass(rootNode)
    }

    private fun hasSwitchClass(node: android.view.accessibility.AccessibilityNodeInfo): Boolean {
        if (node.className?.toString()?.contains("Switch") == true) return true
        for (i in 0 until node.childCount) {
            val child = node.getChild(i) ?: continue
            val found = hasSwitchClass(child)
            child.recycle()
            if (found) return true
        }
        return false
    }

    // Returns the current URL visible in the browser's address bar, or null if not found.
    private fun extractBrowserUrl(pkg: String, rootNode: android.view.accessibility.AccessibilityNodeInfo): String? {
        // Try known view ID first (fast, zero tree traversal)
        val viewId = browserUrlBarIds[pkg]
        if (viewId != null) {
            val nodes = rootNode.findAccessibilityNodeInfosByViewId(viewId)
            if (nodes.isNotEmpty()) {
                val text = nodes[0].text?.toString()
                nodes.forEach { it.recycle() }
                if (!text.isNullOrBlank()) return text
            }
        }
        // Fallback: walk the tree looking for a node whose text looks like a URL.
        // This handles unknown browsers and Chrome's pre-fetch / reader-mode states.
        return findUrlInTree(rootNode)
    }

    private fun findUrlInTree(node: android.view.accessibility.AccessibilityNodeInfo): String? {
        val text = node.text?.toString()
        if (!text.isNullOrBlank() && looksLikeUrl(text)) return text
        for (i in 0 until node.childCount) {
            val child = node.getChild(i) ?: continue
            val found = findUrlInTree(child)
            child.recycle()
            if (found != null) return found
        }
        return null
    }

    private fun looksLikeUrl(text: String): Boolean {
        val t = text.trim()
        return t.startsWith("http://") || t.startsWith("https://") ||
                Regex("^[a-zA-Z0-9.-]+\\.[a-zA-Z]{2,}(/.*)?$").matches(t)
    }

    // Returns true if the URL matches a blocked pattern.
    // Blocked patterns are stored as plain path prefixes, e.g. "instagram.com/reels"
    // or "discord.com/invite". A full domain like "instagram.com" is NOT a match — only
    // subpaths are. Comparison is case-insensitive and ignores the scheme (http/https).
    private fun isUrlBlocked(rawUrl: String, blockedUrls: Set<String>): Boolean {
        if (blockedUrls.isEmpty()) return false

        // Strip scheme and trailing slash for comparison
        val url = rawUrl.trim()
            .removePrefix("https://")
            .removePrefix("http://")
            .trimEnd('/')
            .lowercase()

        for (pattern in blockedUrls) {
            val p = pattern.trim().lowercase().trimEnd('/')
            if (p.isBlank()) continue

            // Only block if the URL starts with the pattern AND the pattern itself contains
            // a path component (i.e. has a "/" in it). This prevents bare-domain entries
            // from accidentally blocking all subpaths — only explicit subpaths are matched.
            if (!p.contains('/')) continue

            if (url == p || url.startsWith("$p/") || url.startsWith("$p?")) {
                Log.d("ContentShield", "URL BLOCKED: $url matched pattern: $p")
                return true
            }
        }
        return false
    }

    override fun onAccessibilityEvent(event: AccessibilityEvent?) {
        if (event?.eventType != AccessibilityEvent.TYPE_WINDOW_STATE_CHANGED &&
            event?.eventType != AccessibilityEvent.TYPE_WINDOW_CONTENT_CHANGED) return

        val pkg = event.packageName?.toString() ?: return

        // --- Settings tamper-protection (existing logic, unchanged) ---
        if (pkg in settingsPackages) {
            if (event.eventType == AccessibilityEvent.TYPE_WINDOW_STATE_CHANGED) {
                val className = event.className?.toString() ?: ""
                val isSubSettingsScreen = className.endsWith("SubSettings")

                Log.d("ContentShield", "Window changed. pkg=$pkg className=$className")

                if (isSubSettingsScreen) {
                    val guardPrefs = getSharedPreferences("ContentShieldPrefs", Context.MODE_PRIVATE)
                    val isUninstallBlocked = guardPrefs.getBoolean("is_uninstall_blocked_enabled", false)

                    if (isUninstallBlocked) {
                        val rootNode = rootInActiveWindow
                        if (rootNode != null) {
                            val label = getServiceDisplayLabel()
                            val labelNodes = rootNode.findAccessibilityNodeInfosByText(label)
                            val hasLabel = labelNodes.isNotEmpty()
                            val hasSwitch = screenContainsSwitch(rootNode)

                            var isResetScreen = false
                            val resetNodesToRecycle = mutableListOf<android.view.accessibility.AccessibilityNodeInfo>()
                            for (anchor in resetScreenAnchors) {
                                val found = rootNode.findAccessibilityNodeInfosByText(anchor)
                                if (found.isNotEmpty()) {
                                    isResetScreen = true
                                    resetNodesToRecycle.addAll(found)
                                }
                            }

                            Log.d("ContentShield", "hasLabel=$hasLabel hasSwitch=$hasSwitch isResetScreen=$isResetScreen")

                            if (hasLabel || isResetScreen) {
                                Log.d("ContentShield", "MATCHED -> kicking home")
                                performGlobalAction(GLOBAL_ACTION_HOME)
                            }

                            labelNodes.forEach { it.recycle() }
                            resetNodesToRecycle.forEach { it.recycle() }
                            rootNode.recycle()
                        }
                    }
                }
            }
            return
        }

        // --- URL blocking (new) ---
        // Fires on both WINDOW_STATE_CHANGED (new tab/navigation) and
        // WINDOW_CONTENT_CHANGED (address bar typed/updated). Both are event-driven.
        if (pkg in browserUrlBarIds || isBrowserPackage(pkg)) {
            val prefs = getSharedPreferences("ContentShieldPrefs", Context.MODE_PRIVATE)
            val blockedUrls = prefs.getStringSet("blocked_urls", emptySet()) ?: emptySet()

            if (blockedUrls.isNotEmpty()) {
                val rootNode = rootInActiveWindow
                if (rootNode != null) {
                    val url = extractBrowserUrl(pkg, rootNode)
                    rootNode.recycle()

                    if (url != null && isUrlBlocked(url, blockedUrls)) {
                        performGlobalAction(GLOBAL_ACTION_BACK)
                    }
                }
            }
            // Don't return here — fall through so app-blocking logic can also run if
            // somehow a browser package is in the blocked_packages list.
        }

        // --- Existing app blocking logic (unchanged) ---
        if (event.eventType != AccessibilityEvent.TYPE_WINDOW_STATE_CHANGED) return
        if (pkg == lastHandledPackage) return
        lastHandledPackage = pkg
        if (pkg == packageName) return

        val prefs = getSharedPreferences("ContentShieldPrefs", Context.MODE_PRIVATE)
        val blockedSet = prefs.getStringSet("blocked_packages", emptySet()) ?: emptySet()
        if (pkg !in blockedSet) return

        if (!::dpm.isInitialized || !dpm.isDeviceOwnerApp(packageName)) return

        performGlobalAction(GLOBAL_ACTION_HOME)

        try {
            dpm.setPackagesSuspended(adminComponent, arrayOf(pkg), true)
        } catch (_: Exception) {}
    }

    // Rough heuristic for detecting unknown browsers not in the map.
    // Checks common browser-related strings in the package name.
    private fun isBrowserPackage(pkg: String): Boolean {
        val lower = pkg.lowercase()
        return lower.contains("browser") || lower.contains("chrome") ||
                lower.contains("firefox") || lower.contains("opera") ||
                lower.contains("safari") || lower.contains("navigator")
    }

    override fun onInterrupt() {}
}
