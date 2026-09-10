package com.example.contentshield

import android.app.Activity
import android.app.AlertDialog
import android.app.admin.DevicePolicyManager
import android.content.ComponentName
import android.content.Context
import android.content.Intent
import android.content.SharedPreferences
import android.graphics.Canvas
import android.graphics.Color
import android.graphics.Paint
import android.graphics.Path
import android.graphics.RectF
import android.graphics.Typeface
import android.graphics.drawable.GradientDrawable
import android.view.WindowInsets
import android.view.WindowManager
import android.os.Build
import android.os.Bundle
import android.os.Handler
import android.os.Looper
import android.os.SystemClock
import android.os.UserManager
import android.provider.Settings
import android.text.TextUtils
import android.view.Gravity
import android.view.MotionEvent
import android.view.View
import android.view.View.GONE
import android.view.View.VISIBLE
import android.view.ViewGroup
import android.view.Window
import android.view.inputmethod.InputMethodManager
import android.widget.ArrayAdapter
import android.widget.Button
import android.widget.EditText
import android.widget.FrameLayout
import android.widget.LinearLayout
import android.widget.ListView
import android.widget.ScrollView
import android.widget.Switch
import android.widget.TextView
import android.net.Uri
import java.io.BufferedReader
import java.io.InputStreamReader
import java.io.OutputStreamWriter
import java.net.HttpURLConnection
import java.net.URL
import java.text.SimpleDateFormat
import java.util.Locale
import org.json.JSONArray
import org.json.JSONObject

// setPackagesSuspended() only works on packages that are currently installed, so:
//  - blocking a package name before it's installed silently fails to actually suspend it
//  - uninstalling a blocked app loses its suspended state, and reinstalling it doesn't restore it
// This receiver listens for PACKAGE_ADDED and re-applies the suspension the moment a
// package that's in our "blocked_packages" set becomes installed (or reinstalled).
// Must also be declared in AndroidManifest.xml - see notes below the class.
// Debug via: adb logcat -s ContentShield
class BlockedPackageInstallReceiver : android.content.BroadcastReceiver() {
    override fun onReceive(context: Context, intent: Intent) {
        if (intent.action != Intent.ACTION_PACKAGE_ADDED) return
        val pkg = intent.data?.schemeSpecificPart ?: return

        val prefs = context.getSharedPreferences("ContentShieldPrefs", Context.MODE_PRIVATE)
        val blockedSet = prefs.getStringSet("blocked_packages", emptySet()) ?: emptySet()
        if (pkg !in blockedSet) return

        val dpm = context.getSystemService(Context.DEVICE_POLICY_SERVICE) as DevicePolicyManager
        val adminComponent = ComponentName(context, MyDeviceAdminReceiver::class.java)
        if (!dpm.isDeviceOwnerApp(context.packageName)) return

        try {
            dpm.setPackagesSuspended(adminComponent, arrayOf(pkg), true)
        } catch (e: Exception) {
            e.printStackTrace()
        }
    }
}

class MainActivity : Activity() {

    private lateinit var dpm: DevicePolicyManager
    private lateinit var adminComponent: ComponentName
    private lateinit var prefs: SharedPreferences

    private val handler = Handler(Looper.getMainLooper())
    private var timerRunnable: Runnable? = null

    // --- Palette (matches reference screenshots) ---
    private val colorBg = Color.parseColor("#121014")
    private val colorCard = Color.parseColor("#1C1A1F")
    private val colorCardAlt = Color.parseColor("#0D0D0F")
    private val colorAccentRed = Color.parseColor("#F2545B")
    private val colorAccentRedDark = Color.parseColor("#331C1C")
    private val colorAccentGray = Color.parseColor("#8E8E93")
    private val colorAccentGrayDark = Color.parseColor("#5A5A5E")
    private val colorAccentGrayDarker = Color.parseColor("#3F3F42")
    private val colorTextMuted = Color.parseColor("#9E9E9E")
    private val colorAmber = Color.parseColor("#FFB74D")
    private val colorTimerText = Color.parseColor("#C4C4C4")
    private val colorGreen = Color.parseColor("#81C784")

    // --- Delay row state ---
    private lateinit var tvDelayValue: TextView
    private lateinit var tvDelayTimerReplace: TextView
    private lateinit var btnDelayEdit: VectorIconView

    // --- Blocklist page state ---
    private lateinit var blockedAppsListContainer: LinearLayout
    private lateinit var blockedAppsScroll: View
    private lateinit var tvBlocklistEmpty: TextView

    // --- URL blocklist state ---
    private lateinit var blockedUrlsListContainer: LinearLayout
    private lateinit var tvUrlBlocklistEmpty: TextView

    // --- Blocklist sub-tab panels ---
    private lateinit var blocklistAppsPanel: View
    private lateinit var blocklistWebsitesPanel: View
    private lateinit var btnBlocklistTabApps: TextView
    private lateinit var btnBlocklistTabWebsites: TextView

    // --- Accessibility warning card ---
    private lateinit var accessibilityWarningCard: LinearLayout

    // --- Tab navigation ---
    private lateinit var pageShielding: View
    private lateinit var pageBlocklist: View
    private lateinit var pageSettings: View
    private lateinit var fabAddPackage: VectorIconView
    private lateinit var navShieldingIcon: VectorIconView
    private lateinit var navShieldingLabel: TextView
    private lateinit var navBlocklistIcon: VectorIconView
    private lateinit var navBlocklistLabel: TextView
    private lateinit var navSettingsIcon: VectorIconView
    private lateinit var navSettingsLabel: TextView
    private lateinit var navShieldingSlot: FrameLayout
    private lateinit var navBlocklistSlot: FrameLayout
    private lateinit var navSettingsSlot: FrameLayout

    private val cardViews = mutableMapOf<String, OptionCardHolder>()

    // Export / Import request codes
    private val REQUEST_EXPORT_BLOCKLIST = 1001
    private val REQUEST_IMPORT_BLOCKLIST = 1002

    // Import countdown state
    private var importCountdownEndTime: Long = 0L
    private var importPendingPackages: Set<String> = emptySet()
    private var importPendingUrls: Set<String> = emptySet()
    private var importCountdownHandler: Handler? = null
    private var importCountdownRunnable: Runnable? = null
    private lateinit var tvImportCountdown: TextView
    private lateinit var btnImportCancel: Button

    // Live view refs per blocked package, so the timer loop can update each row's countdown/abort UI in place
    private val blockedAppRowViews = mutableMapOf<String, BlockedAppRowViews>()
    private val blockedUrlRowViews  = mutableMapOf<String, BlockedUrlRowViews>()

    // Tracks which pending items have already had a single network-time verification
    // attempt fired once their countdown reached zero, so the 1s UI tick doesn't keep
    // re-fetching every second while awaiting/failing verification. Cleared whenever a
    // new countdown is started, or when the user retries after a failed attempt.
    private val endVerificationAttempted = mutableSetOf<String>()
    private val inCountdownMode = mutableSetOf<String>()
    // Persists countdown end times (SystemClock.elapsedRealtime) so timers survive list rebuilds
    private val appCountdownEndTimes = mutableMapOf<String, Long>()
    private val urlCountdownEndTimes = mutableMapOf<String, Long>()

    // Tracks keys currently waiting on the *initial* getNetworkTime() call fired when a
    // countdown is first started (in initiateTurnOffDelay / initiateUnblockDelay /
    // initiateDelayChangeTimer), before is_pending_*_$key has actually been written to
    // prefs yet. Without this, the 1s timer loop can read a stale "not pending" value in
    // the gap between showing the UI and the async network callback landing, and briefly
    // hide the countdown/abort UI before it reappears a moment later. Keys used here are
    // the same namespaced strings already used elsewhere (card key, "unblock_$pkg", or
    // "delay_change"), so there's no collision between the three flows sharing this set.
    private val awaitingInitialFetch = mutableSetOf<String>()

    private class BlockedAppRowViews(
        val tvStatus: TextView,
        val btnCancel: Button,
        val btnApply: Button,
        val btnUnblock: TextView,
        val tvCountdown: TextView
    )

    private class BlockedUrlRowViews(
        val tvStatus: TextView,
        val btnCancel: Button,
        val btnApply: Button,
        val btnRemove: TextView,
        val tvCountdown: TextView
    )

    private class OptionCardHolder(
        val switch: Switch,
        val statusText: TextView,
        val cancelButton: Button,
        val applyButton: Button,
        val enableRestriction: () -> Unit,
        val disableRestriction: () -> Unit,
        val tvTimerReplace: TextView? = null
    )

    // ScrollView that wraps content up to a max height, then scrolls internally beyond that
    private class MaxHeightScrollView(context: Context, private val maxHeightPx: Int) : ScrollView(context) {
        override fun onMeasure(widthMeasureSpec: Int, heightMeasureSpec: Int) {
            val cappedHeightSpec = View.MeasureSpec.makeMeasureSpec(maxHeightPx, View.MeasureSpec.AT_MOST)
            super.onMeasure(widthMeasureSpec, cappedHeightSpec)
        }

        // Since this ScrollView can be nested inside an outer scrolling container, the outer
        // one would otherwise steal every vertical drag before this list gets a chance to
        // scroll. Tell the parent to back off while the user is actively dragging in here.
        override fun onTouchEvent(ev: android.view.MotionEvent): Boolean {
            when (ev.action) {
                android.view.MotionEvent.ACTION_DOWN -> parent.requestDisallowInterceptTouchEvent(true)
                android.view.MotionEvent.ACTION_UP,
                android.view.MotionEvent.ACTION_CANCEL -> parent.requestDisallowInterceptTouchEvent(false)
            }
            return super.onTouchEvent(ev)
        }
    }

    // Simple line-drawn icon glyphs, hand-drawn on a Canvas so they closely match the thin
    // outline reference icons (circled info "i", diagonal pencil, gear) instead of relying on
    // font glyph rendering, which varies by device/font and never quite matches the reference.
    private enum class IconGlyph { INFO, PENCIL, GEAR, SHIELD, BLOCKLIST, CLOSE, PLUS }

    // Minimal SVG path-data ("d" attribute) parser, supporting the M/L/H/V/C/S/Z commands
    // (both absolute and relative) used by the reference icon shapes below. Returns an
    // android.graphics.Path in the SVG's own coordinate space (i.e. matching its viewBox),
    // which callers then scale/translate to fit the target view size.
    private fun parseSvgPath(d: String): Path {
        val path = Path()
        val tokens = Regex("[MmLlHhVvCcSsZz]|-?\\d*\\.?\\d+(?:[eE][-+]?\\d+)?").findAll(d).map { it.value }.toList()
        var i = 0
        var curX = 0f
        var curY = 0f
        var startX = 0f
        var startY = 0f
        var cmd = ' '
        var prevCtrlX = 0f
        var prevCtrlY = 0f
        var prevWasCubic = false

        fun nextNum(): Float = tokens[i++].toFloat()

        while (i < tokens.size) {
            val tok = tokens[i]
            if (tok.length == 1 && tok[0].isLetter()) {
                cmd = tok[0]
                i++
            }
            when (cmd) {
                'M' -> {
                    curX = nextNum(); curY = nextNum()
                    path.moveTo(curX, curY)
                    startX = curX; startY = curY
                    cmd = 'L'; prevWasCubic = false
                }
                'm' -> {
                    curX += nextNum(); curY += nextNum()
                    path.moveTo(curX, curY)
                    startX = curX; startY = curY
                    cmd = 'l'; prevWasCubic = false
                }
                'L' -> { curX = nextNum(); curY = nextNum(); path.lineTo(curX, curY); prevWasCubic = false }
                'l' -> { curX += nextNum(); curY += nextNum(); path.lineTo(curX, curY); prevWasCubic = false }
                'H' -> { curX = nextNum(); path.lineTo(curX, curY); prevWasCubic = false }
                'h' -> { curX += nextNum(); path.lineTo(curX, curY); prevWasCubic = false }
                'V' -> { curY = nextNum(); path.lineTo(curX, curY); prevWasCubic = false }
                'v' -> { curY += nextNum(); path.lineTo(curX, curY); prevWasCubic = false }
                'C' -> {
                    val x1 = nextNum(); val y1 = nextNum()
                    val x2 = nextNum(); val y2 = nextNum()
                    val x = nextNum(); val y = nextNum()
                    path.cubicTo(x1, y1, x2, y2, x, y)
                    prevCtrlX = x2; prevCtrlY = y2
                    curX = x; curY = y
                    prevWasCubic = true
                }
                'c' -> {
                    val x1 = curX + nextNum(); val y1 = curY + nextNum()
                    val x2 = curX + nextNum(); val y2 = curY + nextNum()
                    val x = curX + nextNum(); val y = curY + nextNum()
                    path.cubicTo(x1, y1, x2, y2, x, y)
                    prevCtrlX = x2; prevCtrlY = y2
                    curX = x; curY = y
                    prevWasCubic = true
                }
                'S' -> {
                    val x2 = nextNum(); val y2 = nextNum()
                    val x = nextNum(); val y = nextNum()
                    val x1 = if (prevWasCubic) 2 * curX - prevCtrlX else curX
                    val y1 = if (prevWasCubic) 2 * curY - prevCtrlY else curY
                    path.cubicTo(x1, y1, x2, y2, x, y)
                    prevCtrlX = x2; prevCtrlY = y2
                    curX = x; curY = y
                    prevWasCubic = true
                }
                's' -> {
                    val x2 = curX + nextNum(); val y2 = curY + nextNum()
                    val x = curX + nextNum(); val y = curY + nextNum()
                    val x1 = if (prevWasCubic) 2 * curX - prevCtrlX else curX
                    val y1 = if (prevWasCubic) 2 * curY - prevCtrlY else curY
                    path.cubicTo(x1, y1, x2, y2, x, y)
                    prevCtrlX = x2; prevCtrlY = y2
                    curX = x; curY = y
                    prevWasCubic = true
                }
                'Z', 'z' -> { path.close(); curX = startX; curY = startY; prevWasCubic = false }
            }
        }
        return path
    }

    private inner class VectorIconView(
        context: Context,
        private val glyph: IconGlyph,
        private var iconColor: Int,
        private val strokeWidthFraction: Float = 0.09f
    ) : View(context) {

        private val paint = Paint(Paint.ANTI_ALIAS_FLAG).apply {
            style = Paint.Style.STROKE
            strokeCap = Paint.Cap.ROUND
            strokeJoin = Paint.Join.ROUND
        }
        private val fillPaint = Paint(Paint.ANTI_ALIAS_FLAG).apply {
            style = Paint.Style.FILL
        }

        // Draws an SVG path (given in its own viewBox coordinate space) centered in the view,
        // scaled to fit, either stroked (strokeWidthSvg > 0) or filled.
        private fun drawSvgPath(
            canvas: Canvas,
            svgPath: Path,
            viewBoxSize: Float,
            cx: Float,
            cy: Float,
            size: Float,
            strokeWidthSvg: Float,
            scaleFraction: Float = 0.72f
        ) {
            val scale = (size * scaleFraction) / viewBoxSize
            canvas.save()
            canvas.translate(cx - (viewBoxSize * scale) / 2f, cy - (viewBoxSize * scale) / 2f)
            canvas.scale(scale, scale)
            if (strokeWidthSvg > 0f) {
                paint.color = iconColor
                paint.strokeWidth = strokeWidthSvg
                canvas.drawPath(svgPath, paint)
            } else {
                fillPaint.color = iconColor
                canvas.drawPath(svgPath, fillPaint)
            }
            canvas.restore()
        }

        fun setIconColor(color: Int) {
            iconColor = color
            invalidate()
        }

        override fun onDraw(canvas: Canvas) {
            super.onDraw(canvas)
            val size = minOf(width, height).toFloat()
            if (size <= 0f) return
            val cx = width / 2f
            val cy = height / 2f

            paint.color = iconColor
            paint.strokeWidth = size * strokeWidthFraction
            fillPaint.color = iconColor

            when (glyph) {
                IconGlyph.INFO -> {
                    val r = size * 0.40f
                    canvas.drawCircle(cx, cy, r, paint)
                    canvas.drawCircle(cx, cy - r * 0.45f, size * 0.055f, fillPaint)
                    canvas.drawLine(cx, cy - r * 0.02f, cx, cy + r * 0.48f, paint)
                }
                IconGlyph.PENCIL -> {
                    drawSvgPath(canvas, pencilPath, 20f, cx, cy, size, strokeWidthSvg = 0f)
                }
                IconGlyph.GEAR -> {
                    drawSvgPath(canvas, gearPath, 1920f, cx, cy, size, strokeWidthSvg = 0f)
                }
                IconGlyph.SHIELD -> {
                    drawSvgPath(canvas, shieldPath, 24f, cx, cy, size, strokeWidthSvg = 1.728f)
                }
                IconGlyph.BLOCKLIST -> {
                    drawSvgPath(canvas, blocklistPath, 24f, cx, cy, size, strokeWidthSvg = 2f)
                }
                IconGlyph.CLOSE -> {
                    val r = size * 0.26f
                    canvas.drawLine(cx - r, cy - r, cx + r, cy + r, paint)
                    canvas.drawLine(cx - r, cy + r, cx + r, cy - r, paint)
                }
                IconGlyph.PLUS -> {
                    drawSvgPath(canvas, plusPath, 18f, cx, cy, size, strokeWidthSvg = 0f, scaleFraction = 0.35f)
                }
            }
        }
    }

    // Parsed once and reused across every VectorIconView instance.
    private val shieldPath: Path by lazy {
        parseSvgPath(
            "M20 6C20 6 19.1843 6 19.0001 6C16.2681 6 13.8871 4.93485 11.9999 3C10.1128 4.93478 " +
                    "7.73199 6 5.00009 6C4.81589 6 4.00009 6 4.00009 6C4.00009 6 4 8 4 9.16611C4 14.8596 " +
                    "7.3994 19.6436 12 21C16.6006 19.6436 20 14.8596 20 9.16611C20 8 20 6 20 6Z"
        )
    }
    private val blocklistPath: Path by lazy {
        parseSvgPath(
            "M8 6.00067L21 6.00139M8 12.0007L21 12.0015M8 18.0007L21 18.0015M3.5 6H3.51M3.5 12H3.51" +
                    "M3.5 18H3.51M4 6C4 6.27614 3.77614 6.5 3.5 6.5C3.22386 6.5 3 6.27614 3 6C3 5.72386 " +
                    "3.22386 5.5 3.5 5.5C3.77614 5.5 4 5.72386 4 6ZM4 12C4 12.2761 3.77614 12.5 3.5 12.5" +
                    "C3.22386 12.5 3 12.2761 3 12C3 11.7239 3.22386 11.5 3.5 11.5C3.77614 11.5 4 11.7239 " +
                    "4 12ZM4 18C4 18.2761 3.77614 18.5 3.5 18.5C3.22386 18.5 3 18.2761 3 18C3 17.7239 " +
                    "3.22386 17.5 3.5 17.5C3.77614 17.5 4 17.7239 4 18Z"
        )
    }
    private val gearPath: Path by lazy {
        parseSvgPath(
            "M1703.534 960c0-41.788-3.84-84.48-11.633-127.172l210.184-182.174-199.454-340.856-265.186 " +
                    "88.433c-66.974-55.567-143.323-99.389-223.85-128.415L1158.932 0h-397.78L706.49 269.704c" +
                    "-81.43 29.138-156.423 72.282-223.962 128.414l-265.073-88.32L18 650.654l210.184 182.174" +
                    "C220.39 875.52 216.55 918.212 216.55 960s3.84 84.48 11.633 127.172L18 1269.346l199.454 " +
                    "340.856 265.186-88.433c66.974 55.567 143.322 99.389 223.85 128.415L761.152 1920h397.779" +
                    "l54.663-269.704c81.318-29.138 156.424-72.282 223.963-128.414l265.073 88.433 199.454-" +
                    "340.856-210.184-182.174c7.793-42.805 11.633-85.497 11.633-127.285m-743.492 395.294" +
                    "c-217.976 0-395.294-177.318-395.294-395.294 0-217.976 177.318-395.294 395.294-395.294" +
                    "c217.977 0 395.294 177.318 395.294 395.294 0 217.976-177.317 395.294-395.294 395.294"
        )
    }
    private val pencilPath: Path by lazy {
        parseSvgPath("M12.3 3.7l4 4L4 20H0v-4L12.3 3.7zm1.4-1.4L16 0l4 4-2.3 2.3-4-4z")
    }
    private val plusPath: Path by lazy {
        parseSvgPath(
            "M14.7589286,10.1517857 L10.1517857,10.1517857 L10.1517857,14.7589286 L7.84821429," +
                    "14.7589286 L7.84821429,10.1517857 L3.24107143,10.1517857 L3.24107143,7.84821429 " +
                    "L7.84821429,7.84821429 L7.84821429,3.24107143 L10.1517857,3.24107143 L10.1517857," +
                    "7.84821429 L14.7589286,7.84821429 L14.7589286,10.1517857 Z"
        )
    }

    private fun dp(value: Int): Int = (value * resources.displayMetrics.density).toInt()

    override fun onCreate(savedInstanceState: Bundle?) {
        requestWindowFeature(Window.FEATURE_NO_TITLE)
        super.onCreate(savedInstanceState)

        window.statusBarColor = colorBg

        dpm = getSystemService(Context.DEVICE_POLICY_SERVICE) as DevicePolicyManager
        adminComponent = ComponentName(this, MyDeviceAdminReceiver::class.java)
        prefs = getSharedPreferences("ContentShieldPrefs", Context.MODE_PRIVATE)

        val isDeviceOwner = dpm.isDeviceOwnerApp(packageName)

        // Broadcasts alone aren't reliable enough for this (OS battery/standby rules can defer
        // or drop PACKAGE_ADDED delivery to apps that haven't been opened recently), so every
        // time ContentShield itself is opened we re-apply suspension to everything in
        // blocked_packages. This is what actually guarantees a reinstalled app gets re-blocked.
        resyncBlockedPackages(isDeviceOwner)

        // --- Root: content area (weighted) + fixed bottom nav bar ---
        val root = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            setBackgroundColor(colorBg)
        }

        val contentFrame = FrameLayout(this).apply {
            layoutParams = LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT, 0, 1f
            )
        }

        pageShielding = buildShieldingPage(isDeviceOwner)
        pageBlocklist = buildBlocklistPage(isDeviceOwner)
        pageSettings = buildSettingsPage()

        contentFrame.addView(pageShielding)
        contentFrame.addView(pageBlocklist)
        contentFrame.addView(pageSettings)

        // --- Floating "+" button, only relevant/visible on the Blocklist page ---
        fabAddPackage = VectorIconView(this, IconGlyph.PLUS, Color.WHITE).apply {
            val bg = GradientDrawable().apply {
                setColor(Color.parseColor("#3A363B"))
                shape = GradientDrawable.OVAL
            }
            background = bg
            layoutParams = FrameLayout.LayoutParams(dp(68), dp(68)).apply {
                gravity = Gravity.BOTTOM or Gravity.END
                marginEnd = dp(24)
                bottomMargin = dp(32)
            }
            setOnClickListener {
                if (!checkDeviceOwner(isDeviceOwner)) return@setOnClickListener
                if (::blocklistWebsitesPanel.isInitialized && blocklistWebsitesPanel.visibility == VISIBLE) {
                    showAddUrlDialog()
                } else {
                    showAddPackageDialog(isDeviceOwner)
                }
            }
        }
        contentFrame.addView(fabAddPackage)

        val bottomNav = buildBottomNavBar()

        root.addView(contentFrame)
        root.addView(bottomNav)

        // Pad the content area below the status bar and the nav bar above the gesture/nav bar,
        // so text near the top/bottom never sits flush against the physical screen edge.
        root.setOnApplyWindowInsetsListener { _, insets ->
            val topInset: Int
            val bottomInset: Int
            if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.R) {
                val bars = insets.getInsets(WindowInsets.Type.systemBars())
                topInset = bars.top
                bottomInset = bars.bottom
            } else {
                @Suppress("DEPRECATION")
                topInset = insets.systemWindowInsetTop
                @Suppress("DEPRECATION")
                bottomInset = insets.systemWindowInsetBottom
            }
            contentFrame.setPadding(0, topInset, 0, 0)
            bottomNav.setPadding(bottomNav.paddingLeft, bottomNav.paddingTop, bottomNav.paddingRight, dp(16) + bottomInset)
            insets
        }

        setContentView(root)

        switchTab(Tab.SHIELDING)

        startTimerLoop()
        refreshBlockedAppsList(isDeviceOwner)
        refreshBlockedUrlsList()
        updateAccessibilityWarningUI()
    }

    // =========================================================================================
    // Tab navigation
    // =========================================================================================

    private enum class Tab { SHIELDING, BLOCKLIST, SETTINGS }

    private data class NavItemViews(
        val container: LinearLayout,
        val icon: VectorIconView,
        val label: TextView,
        val iconSlot: FrameLayout
    )

    private fun buildBottomNavBar(): LinearLayout {
        val bar = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            setBackgroundColor(colorCardAlt)
            minimumHeight = dp(76)
            setPadding(0, dp(10), 0, dp(16))
            layoutParams = LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT
            )
        }

        // All three nav tabs use hand-drawn VectorIconView shapes (matching the reference
        // icons) instead of unicode glyphs. Icons sit in a fixed-height pill-shaped slot so
        // tabs with a smaller icon (e.g. Settings) still keep their label on the same line,
        // and so the selected highlight can wrap tightly around just the icon.
        val iconSlotDp = 34
        fun vectorNavItem(glyph: IconGlyph, label: String, iconSizeDp: Int = iconSlotDp): NavItemViews {
            val iconView = VectorIconView(this, glyph, colorTextMuted).apply {
                layoutParams = FrameLayout.LayoutParams(dp(iconSizeDp), dp(iconSizeDp), Gravity.CENTER)
            }
            val iconSlot = FrameLayout(this).apply {
                background = GradientDrawable().apply {
                    setColor(Color.TRANSPARENT)
                    cornerRadius = dp(16).toFloat()
                }
                layoutParams = LinearLayout.LayoutParams(dp(iconSlotDp + 20), dp(iconSlotDp)).apply {
                    bottomMargin = dp(4)
                }
                addView(iconView)
            }
            val tvLabel = TextView(this).apply {
                text = label
                textSize = 11.9f
                gravity = Gravity.CENTER
                setTypeface(null, Typeface.BOLD)
            }
            val item = LinearLayout(this).apply {
                orientation = LinearLayout.VERTICAL
                gravity = Gravity.CENTER
                layoutParams = LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.MATCH_PARENT, 1f)
                addView(iconSlot)
                addView(tvLabel)
            }
            return NavItemViews(item, iconView, tvLabel, iconSlot)
        }

        val (shieldingItem, shieldingIcon, shieldingLabel, shieldingSlot) = vectorNavItem(IconGlyph.SHIELD, "Shield")
        val (blocklistItem, blocklistIcon, blocklistLabel, blocklistSlot) = vectorNavItem(IconGlyph.BLOCKLIST, "Blocklist")
        val (settingsItem, settingsIcon, settingsLabel, settingsSlot) = vectorNavItem(IconGlyph.GEAR, "Settings", iconSizeDp = 24)

        navShieldingIcon = shieldingIcon
        navShieldingLabel = shieldingLabel
        navBlocklistIcon = blocklistIcon
        navBlocklistLabel = blocklistLabel
        navSettingsIcon = settingsIcon
        navSettingsLabel = settingsLabel
        navShieldingSlot = shieldingSlot
        navBlocklistSlot = blocklistSlot
        navSettingsSlot = settingsSlot

        shieldingItem.setOnClickListener { switchTab(Tab.SHIELDING) }
        blocklistItem.setOnClickListener { switchTab(Tab.BLOCKLIST) }
        settingsItem.setOnClickListener { switchTab(Tab.SETTINGS) }

        bar.addView(shieldingItem)
        bar.addView(blocklistItem)
        bar.addView(settingsItem)
        return bar
    }

    private fun switchTab(tab: Tab) {
        pageShielding.visibility = if (tab == Tab.SHIELDING) VISIBLE else GONE
        pageBlocklist.visibility = if (tab == Tab.BLOCKLIST) VISIBLE else GONE
        pageSettings.visibility = if (tab == Tab.SETTINGS) VISIBLE else GONE
        fabAddPackage.visibility = if (tab == Tab.BLOCKLIST) VISIBLE else GONE

        val selectedColor = Color.WHITE
        val unselectedColor = colorTextMuted
        navShieldingIcon.setIconColor(if (tab == Tab.SHIELDING) selectedColor else unselectedColor)
        navShieldingLabel.setTextColor(if (tab == Tab.SHIELDING) selectedColor else unselectedColor)
        navBlocklistIcon.setIconColor(if (tab == Tab.BLOCKLIST) selectedColor else unselectedColor)
        navBlocklistLabel.setTextColor(if (tab == Tab.BLOCKLIST) selectedColor else unselectedColor)
        navSettingsIcon.setIconColor(if (tab == Tab.SETTINGS) selectedColor else unselectedColor)
        navSettingsLabel.setTextColor(if (tab == Tab.SETTINGS) selectedColor else unselectedColor)

        val highlightColor = Color.parseColor("#3A363B")
        fun applyHighlight(slot: FrameLayout, selected: Boolean) {
            slot.background = GradientDrawable().apply {
                setColor(if (selected) highlightColor else Color.TRANSPARENT)
                cornerRadius = dp(16).toFloat()
            }
        }
        applyHighlight(navShieldingSlot, tab == Tab.SHIELDING)
        applyHighlight(navBlocklistSlot, tab == Tab.BLOCKLIST)
        applyHighlight(navSettingsSlot, tab == Tab.SETTINGS)
    }

    // =========================================================================================
    // Shielding page
    // =========================================================================================

    private fun buildShieldingPage(isDeviceOwner: Boolean): View {
        val scrollView = ScrollView(this).apply {
            setBackgroundColor(colorBg)
            isFillViewport = true
            isVerticalScrollBarEnabled = false
        }

        val mainContainer = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            setPadding(dp(20), dp(36), dp(20), dp(56))
        }

        // --- Accessibility warning card, styled like the reference screenshot ---
        accessibilityWarningCard = TextView(this).let { _ -> LinearLayout(this) }.apply {
            orientation = LinearLayout.HORIZONTAL
            gravity = Gravity.CENTER_VERTICAL
            setPadding(dp(14), dp(14), dp(14), dp(14))
            val bg = GradientDrawable().apply {
                setColor(colorAccentRedDark)
                cornerRadius = dp(12).toFloat()
                setStroke(dp(1), colorAccentRed)
            }
            background = bg
            layoutParams = LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT
            ).apply { bottomMargin = dp(16) }
            visibility = GONE
        }

        val warnTextContainer = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            layoutParams = LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f)
        }
        val warnTitle = TextView(this).apply {
            text = "Accessibility is OFF"
            textSize = 16.2f
            setTextColor(Color.WHITE)
            setTypeface(null, Typeface.BOLD)
        }
        val warnSub = TextView(this).apply {
            text = "Some features may not work unless you turn on accessibility service."
            textSize = 13f
            setTextColor(colorTextMuted)
            setPadding(0, dp(4), dp(8), 0)
        }
        warnTextContainer.addView(warnTitle)
        warnTextContainer.addView(warnSub)

        val btnTurnOnAccessibility = Button(this).apply {
            text = "Turn ON"
            textSize = 11.9f
            setTextColor(colorAccentRed)
            setTypeface(null, Typeface.BOLD)
            gravity = Gravity.CENTER
            val bg = GradientDrawable().apply {
                setColor(Color.TRANSPARENT)
                cornerRadius = dp(20).toFloat()
                setStroke(dp(1), colorAccentRed)
            }
            background = bg
            setPadding(dp(14), dp(6), dp(14), dp(6))
            setOnClickListener { openAccessibilityServiceSettings() }
        }

        accessibilityWarningCard.addView(warnTextContainer)
        accessibilityWarningCard.addView(btnTurnOnAccessibility)
        accessibilityWarningCard.setOnClickListener { openAccessibilityServiceSettings() }

        mainContainer.addView(accessibilityWarningCard)

        // --- Grouped "Shielding" section, styled like the reference "Content Blocking" group ---
        val sectionLabelIcon = VectorIconView(this, IconGlyph.SHIELD, Color.WHITE).apply {
            layoutParams = LinearLayout.LayoutParams(dp(30), dp(30)).apply { rightMargin = dp(6) }
        }
        val sectionLabelText = TextView(this).apply {
            text = "Shield Controls"
            textSize = 16f
            setTextColor(Color.WHITE)
            setTypeface(null, Typeface.BOLD)
        }
        val sectionLabel = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            gravity = Gravity.CENTER_VERTICAL
            setPadding(dp(16), dp(6), dp(16), dp(6))
            setBackgroundColor(Color.parseColor("#2A272C"))
            layoutParams = LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT
            )
            addView(sectionLabelIcon)
            addView(sectionLabelText)
        }

        val groupCard = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            setPadding(dp(16), dp(6), dp(16), dp(6))
            val bg = GradientDrawable().apply {
                setColor(colorCard)
                setStroke(dp(1), Color.parseColor("#332E33"))
                val r = dp(12).toFloat()
                // Top corners square (flush with header), bottom corners rounded
                cornerRadii = floatArrayOf(0f, 0f, 0f, 0f, r, r, r, r)
            }
            background = bg
            layoutParams = LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT
            )
        }

        // Header + card are wrapped in a single container whose rounded outline is used to
        // clip both children together. This avoids the two separate GradientDrawables (each
        // rounding only some of their own corners) ever producing a seam/gap where they meet.
        val shieldControlsGroup = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            background = GradientDrawable().apply {
                setColor(Color.TRANSPARENT)
                cornerRadius = dp(12).toFloat()
            }
            clipToOutline = true
            layoutParams = LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT
            ).apply { bottomMargin = dp(24) }
            addView(sectionLabel)
            addView(groupCard)
        }


        // --- Delay row (replaces "Accountability Partner") ---
        groupCard.addView(buildDelayRow(isDeviceOwner))
        groupCard.addView(divider())

        // --- Check current system restriction states ---
        val userRestrictions = try {
            if (isDeviceOwner) dpm.getUserRestrictions(adminComponent) else Bundle()
        } catch (e: Exception) {
            Bundle()
        }

        val isDnsLocked = userRestrictions.getBoolean(UserManager.DISALLOW_CONFIG_PRIVATE_DNS, false)
        val isInstallBlocked = userRestrictions.getBoolean(UserManager.DISALLOW_INSTALL_APPS, false)
        val isSafeBootBlocked = userRestrictions.getBoolean(UserManager.DISALLOW_SAFE_BOOT, false)
        val isUninstallBlocked = try {
            if (isDeviceOwner) dpm.isUninstallBlocked(adminComponent, packageName) else false
        } catch (e: Exception) {
            false
        }
        val isAddUserBlocked = userRestrictions.getBoolean(UserManager.DISALLOW_ADD_USER, false)

        val cardDns = buildToggleRow(
            key = "dns",
            title = "Lock DNS & VPN",
            subtitle = "Prevents modifying Private DNS settings or connecting unauthorized VPNs",
            initialState = isDnsLocked,
            isDeviceOwner = isDeviceOwner,
            onEnable = {
                dpm.addUserRestriction(adminComponent, UserManager.DISALLOW_CONFIG_PRIVATE_DNS)
                dpm.addUserRestriction(adminComponent, UserManager.DISALLOW_CONFIG_VPN)
                if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.Q) {
                    try {
                        dpm.setGlobalPrivateDnsModeSpecifiedHost(adminComponent, "dns.adguard-dns.com")
                    } catch (_: Exception) {}
                }
            },
            onDisable = {
                dpm.clearUserRestriction(adminComponent, UserManager.DISALLOW_CONFIG_PRIVATE_DNS)
                dpm.clearUserRestriction(adminComponent, UserManager.DISALLOW_CONFIG_VPN)
            }
        )

        val cardPreventInstall = buildToggleRow(
            key = "prevent_install",
            title = "Block app installations",
            subtitle = "Prevents downloading or installing any new apps from Google Play or APK files",
            initialState = isInstallBlocked,
            isDeviceOwner = isDeviceOwner,
            onEnable = {
                dpm.addUserRestriction(adminComponent, UserManager.DISALLOW_INSTALL_APPS)
                dpm.addUserRestriction(adminComponent, UserManager.DISALLOW_INSTALL_UNKNOWN_SOURCES)
            },
            onDisable = {
                dpm.clearUserRestriction(adminComponent, UserManager.DISALLOW_INSTALL_APPS)
                dpm.clearUserRestriction(adminComponent, UserManager.DISALLOW_INSTALL_UNKNOWN_SOURCES)
            }
        )

        val cardSafeBoot = buildToggleRow(
            key = "safeboot",
            title = "Block safe mode",
            subtitle = "Disables booting the phone into Safe Mode to bypass restrictions",
            initialState = isSafeBootBlocked,
            isDeviceOwner = isDeviceOwner,
            onEnable = { dpm.addUserRestriction(adminComponent, UserManager.DISALLOW_SAFE_BOOT) },
            onDisable = { dpm.clearUserRestriction(adminComponent, UserManager.DISALLOW_SAFE_BOOT) }
        )

        val cardUninstall = buildToggleRow(
            key = "uninstall",
            title = "Uninstall protection",
            subtitle = "Blocks removing, stopping, or wiping Content Shield via Settings or external ADB commands",
            initialState = isUninstallBlocked,
            isDeviceOwner = isDeviceOwner,
            onEnable = {
                dpm.setUninstallBlocked(adminComponent, packageName, true)
                if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.R) {
                    dpm.setUserControlDisabledPackages(adminComponent, listOf(packageName))
                }
                dpm.addUserRestriction(adminComponent, UserManager.DISALLOW_APPS_CONTROL)

                // Locks which accessibility services are allowed to be configured at all.
                // Passing only our own package means no accessibility service (including ours)
                // can be freely toggled off through the Settings UI while this is active.
                try {
                    dpm.setPermittedAccessibilityServices(adminComponent, listOf(packageName))
                } catch (_: Exception) {}

                // Save the state so the Accessibility Service can detect the protection
                prefs.edit().putBoolean("is_uninstall_blocked_enabled", true).apply()
            },
            onDisable = {
                dpm.setUninstallBlocked(adminComponent, packageName, false)
                if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.R) {
                    dpm.setUserControlDisabledPackages(adminComponent, emptyList())
                }
                dpm.clearUserRestriction(adminComponent, UserManager.DISALLOW_APPS_CONTROL)

                // null clears the restriction, allowing any accessibility service again
                try {
                    dpm.setPermittedAccessibilityServices(adminComponent, null)
                } catch (_: Exception) {}

                // Update the state
                prefs.edit().putBoolean("is_uninstall_blocked_enabled", false).apply()
            }
        )

        val cardAddUser = buildToggleRow(
            key = "adduser",
            title = "Disable guest accounts",
            subtitle = "Prevents creating secondary profiles to bypass restrictions",
            initialState = isAddUserBlocked,
            isDeviceOwner = isDeviceOwner,
            onEnable = { dpm.addUserRestriction(adminComponent, UserManager.DISALLOW_ADD_USER) },
            onDisable = { dpm.clearUserRestriction(adminComponent, UserManager.DISALLOW_ADD_USER) }
        )

        groupCard.addView(cardDns)
        groupCard.addView(divider())
        groupCard.addView(cardPreventInstall)
        groupCard.addView(divider())
        groupCard.addView(cardSafeBoot)
        groupCard.addView(divider())
        groupCard.addView(cardUninstall)
        groupCard.addView(divider())
        groupCard.addView(cardAddUser)

        mainContainer.addView(shieldControlsGroup)

        scrollView.addView(mainContainer)
        return scrollView
    }

    private fun divider(): View = View(this).apply {
        layoutParams = LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, dp(1)).apply {
            topMargin = dp(4); bottomMargin = dp(4)
        }
        setBackgroundColor(Color.parseColor("#2A272C"))
    }

    // All AlertDialogs in the app go through these two helpers instead of a bare
    // AlertDialog.Builder(this), so every popup matches the app's dark theme instead of
    // falling back to the stock (light) system dialog theme.
    private fun themedDialogBuilder(): AlertDialog.Builder {
        return AlertDialog.Builder(this, android.R.style.Theme_DeviceDefault_Dialog_Alert)
    }

    private fun applyDialogTheme(dialog: AlertDialog) {
        dialog.window?.setBackgroundDrawable(GradientDrawable().apply {
            setColor(colorCard)
            cornerRadius = dp(14).toFloat()
        })
        dialog.window?.let { window ->
            val params = window.attributes
            params.y -= dp(24)
            window.attributes = params
        }
        dialog.setOnShowListener {
            dialog.getButton(AlertDialog.BUTTON_POSITIVE)?.setTextColor(Color.WHITE)
            dialog.getButton(AlertDialog.BUTTON_NEGATIVE)?.setTextColor(colorTextMuted)
            dialog.getButton(AlertDialog.BUTTON_NEUTRAL)?.setTextColor(colorTextMuted)
        }
    }

    // Builds a title + message pair styled to match the app instead of relying on the
    // system AlertDialog's built-in (light-themed) title/message views.
    private fun themedDialogContent(title: String, message: String? = null, extra: View? = null): View {
        val container = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            setPadding(dp(24), dp(20), dp(24), dp(20))
        }
        val tvTitle = TextView(this).apply {
            text = title
            textSize = 17f
            setTextColor(Color.WHITE)
            setTypeface(null, Typeface.BOLD)
        }
        container.addView(tvTitle)
        if (message != null) {
            val tvMessage = TextView(this).apply {
                text = message
                textSize = 14.5f
                setTextColor(colorTextMuted)
                setPadding(0, dp(10), 0, 0)
            }
            container.addView(tvMessage)
        }
        if (extra != null) container.addView(extra)
        return container
    }

    // Small circular "i" button that shows the row's description in a dialog, instead of
    // always rendering the subtitle text inline (matches the reference screenshot's info icons).
    private fun infoButton(title: String, message: String): View {
        return VectorIconView(this, IconGlyph.INFO, colorTextMuted).apply {
            layoutParams = LinearLayout.LayoutParams(dp(22), dp(22)).apply { marginStart = dp(10) }
            setOnClickListener {
                val dialog = themedDialogBuilder()
                    .setView(themedDialogContent(title, message))
                    .setPositiveButton("Got it", null)
                    .create()
                applyDialogTheme(dialog)
                dialog.show()
            }
        }
    }

    // --- Delay row UI & logic ---
    private fun buildDelayRow(isDeviceOwner: Boolean): LinearLayout {
        val wrapper = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            setPadding(0, dp(12), 0, dp(12))
        }

        val topRow = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            gravity = Gravity.CENTER_VERTICAL
        }

        val textContainer = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            layoutParams = LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f)
        }

        val tvTitle = TextView(this).apply {
            text = "Delay"
            textSize = 17.3f
            setTextColor(Color.WHITE)
            setTypeface(null, Typeface.BOLD)
        }

        tvDelayValue = TextView(this).apply {
            text = "${prefs.getInt("saved_delay_minutes", 30)} minutes"
            textSize = 13f
            setTextColor(colorTextMuted)
            setPadding(0, dp(2), 0, 0)
        }

        textContainer.addView(tvTitle)
        textContainer.addView(tvDelayValue)

        // Timer shown in the top row while a delay change is counting down.
        // Sits immediately left of the pencil (matching the position of timers in other
        // shield-control rows). Pencil goes GONE while timer is VISIBLE and returns when done.
        tvDelayTimerReplace = TextView(this).apply {
            text = "00:00:00"
            textSize = 15f
            setTextColor(colorTimerText)
            setTypeface(null, Typeface.BOLD)
            includeFontPadding = false
            gravity = Gravity.CENTER_VERTICAL
            visibility = GONE
            layoutParams = LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT
            ).apply { marginEnd = dp(8) }
        }

        btnDelayEdit = VectorIconView(this, IconGlyph.PENCIL, colorTextMuted).apply {
            layoutParams = LinearLayout.LayoutParams(dp(22), dp(22))
            setOnClickListener {
                if (checkDeviceOwner(isDeviceOwner)) showEditDelayDialog()
            }
        }

        topRow.addView(textContainer)
        topRow.addView(tvDelayTimerReplace)
        topRow.addView(btnDelayEdit)

        wrapper.addView(topRow)
        return wrapper
    }

    private fun showEditDelayDialog() {
        val container = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            setPadding(dp(24), dp(16), dp(24), dp(0))
            gravity = Gravity.CENTER_VERTICAL
        }
        val input = EditText(this).apply {
            inputType = android.text.InputType.TYPE_CLASS_NUMBER
            setText(prefs.getInt("saved_delay_minutes", 30).toString())
            setTextColor(Color.WHITE)
            setSelection(text.length)
        }
        container.addView(input)
        val tvUnit = TextView(this).apply {
            text = "minutes"
            setTextColor(Color.WHITE)
            setPadding(dp(8), 0, 0, 0)
        }
        container.addView(tvUnit)
        container.layoutParams = LinearLayout.LayoutParams(
            ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT
        ).apply { bottomMargin = dp(24) }

        val dialog = themedDialogBuilder()
            .setView(themedDialogContent(
                "Set delay",
                "How long should it take for requested changes to take effect?",
                container
            ))
            .setPositiveButton("Save") { _, _ ->
                val newMinutes = input.text.toString().toIntOrNull() ?: 0
                val targetMinutes = if (newMinutes < 0) 0 else newMinutes
                val currentActiveDelay = prefs.getInt("saved_delay_minutes", 30)

                if (targetMinutes == currentActiveDelay) return@setPositiveButton

                if (currentActiveDelay <= 0) {
                    prefs.edit().putInt("saved_delay_minutes", targetMinutes).apply()
                    tvDelayValue.text = "$targetMinutes minutes"
                    tvDelayTimerReplace.visibility = GONE
                    btnDelayEdit.visibility = VISIBLE
                } else {
                    initiateDelayChangeTimer(currentActiveDelay, targetMinutes)
                }
            }
            .setNegativeButton("Cancel", null)
            .create()
        applyDialogTheme(dialog)
        dialog.window?.setSoftInputMode(WindowManager.LayoutParams.SOFT_INPUT_ADJUST_RESIZE)
        dialog.show()
    }

    private fun buildToggleRow(
        key: String,
        title: String,
        subtitle: String,
        initialState: Boolean,
        isDeviceOwner: Boolean,
        onEnable: () -> Unit,
        onDisable: () -> Unit
    ): LinearLayout {
        val wrapper = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            setPadding(0, dp(12), 0, dp(12))
        }

        val topRow = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            gravity = Gravity.CENTER_VERTICAL
        }

        val tvTitle = TextView(this).apply {
            text = title
            textSize = 17.3f
            setTextColor(Color.WHITE)
            layoutParams = LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f)
        }

        val toggleSwitch = Switch(this).apply {
            isChecked = initialState
            val states = arrayOf(
                intArrayOf(android.R.attr.state_checked),
                intArrayOf(-android.R.attr.state_checked)
            )
            thumbTintList = android.content.res.ColorStateList(
                states, intArrayOf(Color.WHITE, Color.parseColor("#BDBDBD"))
            )
            // Note: tinting the stock track drawable (trackTintList) doesn't work well here —
            // the system track drawable bakes in a low alpha of its own, so even a vivid hex
            // tint still renders washed-out/gray once blended. Using a fully opaque custom
            // drawable per state instead guarantees a true, solid material green.
            trackDrawable = android.graphics.drawable.StateListDrawable().apply {
                addState(intArrayOf(android.R.attr.state_checked), GradientDrawable().apply {
                    shape = GradientDrawable.RECTANGLE
                    cornerRadius = dp(999).toFloat()
                    setColor(Color.parseColor("#0FDB6E"))
                })
                addState(intArrayOf(-android.R.attr.state_checked), GradientDrawable().apply {
                    shape = GradientDrawable.RECTANGLE
                    cornerRadius = dp(999).toFloat()
                    setColor(colorTextMuted)
                })
            }
        }

        val btnInfo = infoButton(title, subtitle)

        // Timer that replaces the toggle switch while a turn-off delay is counting down
        val tvTimerReplace = TextView(this).apply {
            text = "00:00:00"  // placeholder text so the FrameLayout has a stable width
            textSize = 15f
            setTextColor(Color.WHITE)
            setTypeface(null, Typeface.BOLD)
            includeFontPadding = false
            gravity = Gravity.CENTER_VERTICAL
            visibility = View.INVISIBLE  // INVISIBLE (not GONE) so FrameLayout holds its size
            layoutParams = LinearLayout.LayoutParams(ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT).apply {
                marginEnd = dp(6)
            }
        }

        // Wrap switch + timer in a FrameLayout so toggling between them doesn't
        // change the row's height (one stays INVISIBLE while the other is VISIBLE,
        // preventing vertical layout jumps when the timer appears/disappears).
        val switchTimerFrame = FrameLayout(this).apply {
            layoutParams = LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT
            )
        }
        tvTimerReplace.layoutParams = FrameLayout.LayoutParams(
            ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT,
            Gravity.CENTER_VERTICAL
        ).apply { marginEnd = dp(6) }
        toggleSwitch.layoutParams = FrameLayout.LayoutParams(
            ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT,
            Gravity.CENTER_VERTICAL
        )
        switchTimerFrame.addView(tvTimerReplace)
        switchTimerFrame.addView(toggleSwitch)

        topRow.addView(tvTitle)
        topRow.addView(switchTimerFrame)
        topRow.addView(btnInfo)

        val tvStatus = TextView(this).apply {
            text = ""
            textSize = 11.9f
            setTextColor(colorAmber)
            setPadding(0, dp(8), 0, 0)
            visibility = GONE
        }

        val actionRow = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            layoutParams = LinearLayout.LayoutParams(ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT).apply { topMargin = dp(8) }
        }

        val btnCancel = Button(this).apply {
            text = "Cancel"
            textSize = 10.8f
            setTextColor(Color.parseColor("#E57373"))
            val bg = GradientDrawable().apply {
                setColor(colorAccentRedDark)
                cornerRadius = dp(6).toFloat()
            }
            background = bg
            setPadding(dp(8), dp(2), dp(8), dp(2))
            visibility = GONE
            layoutParams = LinearLayout.LayoutParams(ViewGroup.LayoutParams.WRAP_CONTENT, dp(30))
        }

        val btnApply = Button(this).apply {
            text = "Confirm"
            textSize = 10.8f
            setTextColor(colorGreen)
            val bg = GradientDrawable().apply {
                setColor(Color.parseColor("#1B2E1E"))
                cornerRadius = dp(6).toFloat()
            }
            background = bg
            setPadding(dp(8), dp(2), dp(8), dp(2))
            visibility = GONE
            layoutParams = LinearLayout.LayoutParams(ViewGroup.LayoutParams.WRAP_CONTENT, dp(30)).apply { marginStart = dp(8) }
        }

        actionRow.addView(btnCancel)
        actionRow.addView(btnApply)

        val holder = OptionCardHolder(toggleSwitch, tvStatus, btnCancel, btnApply, onEnable, onDisable, tvTimerReplace)
        cardViews[key] = holder

        // Switch taps are handled via a touch listener instead of a click listener so we can
        // consume the touch outright and decide the visual end-state ourselves. Letting the
        // Switch handle the tap normally means it immediately animates its own thumb/track to
        // the new position *before* our listener runs; when we then need to revert it (e.g.
        // turning off requires a delay), snapping it back a frame later reads as a flicker.
        // Intercepting the touch means the widget's thumb never moves until we say so.
        toggleSwitch.setOnTouchListener { _, event ->
            if (event.actionMasked == MotionEvent.ACTION_UP) {
                handleSwitchTap(key, toggleSwitch, holder, isDeviceOwner)
            }
            true
        }

        // btnCancel and btnApply are no longer added to the view hierarchy for toggle rows,
        // but are kept on the holder for any legacy code paths that may reference them.

        wrapper.addView(topRow)
        return wrapper
    }

    // Applies the tap: userWantsOn is the state the user is asking to move TO (the inverse
    // of the switch's current isChecked, since we intercept the touch before Android's own
    // toggle logic ever runs).
    private fun handleSwitchTap(key: String, toggleSwitch: Switch, holder: OptionCardHolder, isDeviceOwner: Boolean) {
        if (!checkDeviceOwner(isDeviceOwner)) return

        val userWantsOn = !toggleSwitch.isChecked

        if (userWantsOn) {
            cancelPendingOff(key)
            endVerificationAttempted.remove(key)
            try {
                holder.enableRestriction()
                toggleSwitch.isChecked = true
            } catch (e: Exception) {
                toggleSwitch.isChecked = false
            }
        } else {
            val activeDelayMinutes = prefs.getInt("saved_delay_minutes", 30)
            // Keep the switch visually ON the whole time it's pending; only the confirmed
            // apply actually flips it off. jumpDrawablesToCurrentState() avoids any
            // animation, since isChecked never actually left true here.
            toggleSwitch.isChecked = true
            toggleSwitch.jumpDrawablesToCurrentState()
            if (activeDelayMinutes <= 0) {
                // Delay=0: show 00:00:00 timer immediately, locked until user taps it.
                // Tapping shows a confirm dialog; Cancel restores the switch.
                holder.switch.visibility = View.INVISIBLE
                holder.tvTimerReplace?.text = "00:00:00"
                holder.tvTimerReplace?.setTextColor(colorTimerText)
                holder.tvTimerReplace?.visibility = VISIBLE
                holder.tvTimerReplace?.setOnClickListener {
                    themedDialogBuilder()
                        .setView(themedDialogContent(
                            "Turn off?",
                            "Are you sure you want to turn this off?"
                        ))
                        .setPositiveButton("Confirm") { _, _ ->
                            try {
                                holder.disableRestriction()
                                holder.tvTimerReplace?.visibility = View.INVISIBLE
                                holder.switch.visibility = VISIBLE
                                holder.switch.isChecked = false
                            } catch (e: Exception) {
                                holder.tvTimerReplace?.visibility = View.INVISIBLE
                                holder.switch.visibility = VISIBLE
                                holder.switch.isChecked = true
                            }
                        }
                        .setNegativeButton("Cancel") { _, _ ->
                            // Restore the toggle switch
                            holder.tvTimerReplace?.visibility = View.INVISIBLE
                            holder.switch.visibility = VISIBLE
                        }
                        .let { builder -> val d = builder.create(); applyDialogTheme(d); d }
                        .show()
                }
            } else {
                initiateTurnOffDelay(key, activeDelayMinutes, holder)
            }
        }
    }

    // =========================================================================================
    // Blocklist page
    // =========================================================================================

    private fun buildBlocklistPage(isDeviceOwner: Boolean): View {
        // Outer frame — full-page, no scrolling at this level
        val frame = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            setBackgroundColor(colorBg)
            layoutParams = ViewGroup.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT
            )
        }

        // Sub-tab pill track — colorAccentGrayDarker gives visible depth against colorBg
        val tabTrack = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            gravity = Gravity.CENTER_VERTICAL
            background = GradientDrawable().apply {
                setColor(colorCard)
                cornerRadius = dp(50).toFloat()
            }
            layoutParams = LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT, dp(44)
            ).apply { topMargin = dp(16); leftMargin = dp(20); rightMargin = dp(20) }
            setPadding(dp(4), dp(4), dp(4), dp(4))
        }

        fun makeTabLabel(text: String): TextView = TextView(this).apply {
            this.text = text
            textSize = 15.5f
            setTypeface(null, Typeface.BOLD)
            gravity = Gravity.CENTER
            layoutParams = LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.MATCH_PARENT, 1f)
        }
        btnBlocklistTabApps     = makeTabLabel("Apps")
        btnBlocklistTabWebsites = makeTabLabel("Websites")
        tabTrack.addView(btnBlocklistTabApps)
        tabTrack.addView(btnBlocklistTabWebsites)
        frame.addView(tabTrack)

        // ── Apps panel ───────────────────────────────────────────────────
        val appsScroll = ScrollView(this).apply {
            setBackgroundColor(colorBg)
            isFillViewport = true
            isVerticalScrollBarEnabled = false
            layoutParams = LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT, 0, 1f
            )
        }
        val appsContainer = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            setPadding(dp(20), dp(20), dp(20), dp(100))
        }
        blockedAppsListContainer = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            layoutParams = LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT
            )
        }
        blockedAppsScroll = blockedAppsListContainer
        tvBlocklistEmpty = TextView(this).apply {
            text = "Empty List"
            textSize = 15.1f
            setTextColor(colorTextMuted)
            gravity = Gravity.CENTER
            setPadding(0, dp(80), 0, 0)
            visibility = GONE
        }
        appsContainer.addView(blockedAppsListContainer)
        appsContainer.addView(tvBlocklistEmpty)
        appsScroll.addView(appsContainer)
        blocklistAppsPanel = appsScroll

        // ── Websites panel ───────────────────────────────────────────────
        val webScroll = ScrollView(this).apply {
            setBackgroundColor(colorBg)
            isFillViewport = true
            isVerticalScrollBarEnabled = false
            layoutParams = LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT, 0, 1f
            )
        }
        val webContainer = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            setPadding(dp(20), dp(20), dp(20), dp(100))
        }
        blockedUrlsListContainer = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            layoutParams = LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT
            )
        }
        tvUrlBlocklistEmpty = TextView(this).apply {
            text = "Empty List"
            textSize = 15.1f
            setTextColor(colorTextMuted)
            gravity = Gravity.CENTER
            setPadding(0, dp(80), 0, 0)
            visibility = GONE
        }
        webContainer.addView(blockedUrlsListContainer)
        webContainer.addView(tvUrlBlocklistEmpty)
        webScroll.addView(webContainer)
        blocklistWebsitesPanel = webScroll

        frame.addView(blocklistAppsPanel)
        frame.addView(blocklistWebsitesPanel)

        // Wire tab clicks
        fun selectBlocklistTab(appsSelected: Boolean) {
            // Track = colorAccentGrayDarker (#3F3F42), pill = colorAccentGrayDark (#5A5A5E)
            // Selected text = WHITE, unselected = colorTextMuted
            val activePill = GradientDrawable().apply {
                setColor(Color.parseColor("#3A363B"))
                cornerRadius = dp(50).toFloat()
            }
            btnBlocklistTabApps.background     = if (appsSelected) activePill else null
            btnBlocklistTabWebsites.background = if (!appsSelected) GradientDrawable().apply {
                setColor(Color.parseColor("#3A363B")); cornerRadius = dp(50).toFloat()
            } else null
            btnBlocklistTabApps.setTextColor(if (appsSelected) Color.WHITE else colorTextMuted)
            btnBlocklistTabWebsites.setTextColor(if (!appsSelected) Color.WHITE else colorTextMuted)
            blocklistAppsPanel.visibility     = if (appsSelected) VISIBLE else GONE
            blocklistWebsitesPanel.visibility = if (!appsSelected) VISIBLE else GONE
        }
        btnBlocklistTabApps.setOnClickListener     { selectBlocklistTab(true) }
        btnBlocklistTabWebsites.setOnClickListener { selectBlocklistTab(false) }
        selectBlocklistTab(true)

        return frame
    }

    private fun showAddPackageDialog(isDeviceOwner: Boolean) {
        val container = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            setPadding(dp(24), dp(16), dp(24), dp(20))
        }

        val etManualPackage = EditText(this).apply {
            hint = "com.example.app"
            setTextColor(Color.WHITE)
            setHintTextColor(Color.GRAY)
        }
        container.addView(etManualPackage)

        val btnPickApp = Button(this).apply {
            text = "Select From Installed Apps"
            setTextColor(Color.WHITE)
            textSize = 13f
            setTypeface(null, Typeface.BOLD)
            val bg = GradientDrawable().apply {
                setColor(Color.parseColor("#2A282E"))
                cornerRadius = dp(8).toFloat()
            }
            background = bg
            layoutParams = LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT
            ).apply { topMargin = dp(14) }
        }
        container.addView(btnPickApp)

        val dialog = themedDialogBuilder()
            .setView(themedDialogContent("Block an app", extra = container))
            .setPositiveButton("Block") { _, _ ->
                val pkg = etManualPackage.text.toString().trim()
                if (pkg.isNotEmpty()) suspendPackage(pkg)
            }
            .setNegativeButton("Cancel", null)
            .create()
        applyDialogTheme(dialog)

        btnPickApp.setOnClickListener {
            dialog.dismiss()
            showInstalledAppsDialog()
        }

        dialog.show()
    }

    private fun showInstalledAppsDialog() {
        val pm = packageManager
        val mainIntent = Intent(Intent.ACTION_MAIN, null).apply {
            addCategory(Intent.CATEGORY_LAUNCHER)
        }

        val resolvedApps = pm.queryIntentActivities(mainIntent, 0)
            .map { it.activityInfo.packageName }
            .distinct()
            .filter { it != packageName }
            .sorted()

        val appDisplayList = resolvedApps.map { pkg ->
            val appName = try {
                pm.getApplicationLabel(pm.getApplicationInfo(pkg, 0)).toString()
            } catch (e: Exception) {
                pkg
            }
            "$appName ($pkg)"
        }.toTypedArray()

        val listView = ListView(this).apply {
            layoutParams = LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT
            )
            adapter = object : ArrayAdapter<String>(this@MainActivity, 0, appDisplayList) {
                override fun getView(position: Int, convertView: View?, parent: ViewGroup): View {
                    val tv = (convertView as? TextView) ?: TextView(this@MainActivity).apply {
                        setPadding(dp(4), dp(14), dp(4), dp(14))
                        textSize = 14.5f
                    }
                    tv.text = getItem(position)
                    tv.setTextColor(Color.WHITE)
                    return tv
                }
            }
            divider = GradientDrawable().apply { setColor(Color.parseColor("#332E33")) }
            dividerHeight = dp(1)
        }

        val dialog = themedDialogBuilder()
            .setView(themedDialogContent("Select App to Block", extra = listView))
            .setNegativeButton("Cancel", null)
            .create()
        applyDialogTheme(dialog)

        listView.setOnItemClickListener { _, _, which, _ ->
            suspendPackage(resolvedApps[which])
            dialog.dismiss()
        }

        dialog.show()
    }

    // =========================================================================================
    // Settings page
    // =========================================================================================

    private fun buildSettingsPage(): View {
        val scrollView = ScrollView(this).apply {
            setBackgroundColor(colorBg)
            isFillViewport = true
            isVerticalScrollBarEnabled = false
        }

        val mainContainer = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            setPadding(dp(26), dp(22), dp(26), dp(56))
        }

        val settingsCard = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            layoutParams = LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT
            )
        }

        val rowTextColor = Color.parseColor("#EDECED")
        val rowPadV = dp(7)
        val exitPadV = dp(14)
        // Total horizontal space consumed by the chevron before the label:
        // marginStart(20) + glyph natural width (~18dp at 31sp) + marginEnd(16) ≈ 54dp fixed.
        // We replicate this exactly for the exit icon so "Exit" aligns with other labels.
        val iconSlotWidth = dp(54)

        // ── Shared row builder: chevron-icon on left, label, optional right slot ──
        fun makeIconRow(
            iconText: String,
            label: String,
            onClick: () -> Unit
        ): Pair<LinearLayout, FrameLayout> {
            val tvIcon = TextView(this).apply {
                text = iconText
                textSize = 31f
                setTextColor(Color.parseColor("#C0C0C5"))
                setTypeface(null, Typeface.BOLD)
                includeFontPadding = false
                gravity = Gravity.CENTER_VERTICAL
                layoutParams = LinearLayout.LayoutParams(
                    ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT
                ).apply { marginStart = dp(20); marginEnd = dp(16) }
            }
            val tvLabel = TextView(this).apply {
                text = label
                textSize = 17.3f
                setTextColor(rowTextColor)
                layoutParams = LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f).apply {
                    marginStart = dp(8)
                }
            }
            val rightSlot = FrameLayout(this).apply {
                layoutParams = LinearLayout.LayoutParams(
                    ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT
                )
            }
            val row = LinearLayout(this).apply {
                orientation = LinearLayout.HORIZONTAL
                gravity = Gravity.CENTER_VERTICAL
                setPadding(0, rowPadV, 0, rowPadV)
                isClickable = true
                isFocusable = true
                addView(tvIcon)
                addView(tvLabel)
                addView(rightSlot)
                setOnClickListener { onClick() }
            }
            return row to rightSlot
        }

        // ── Export row ────────────────────────────────────────────────────
        val (rowExport, _) = makeIconRow("›", "Export Blocklist") { exportBlocklist() }

        // ── Import row — right slot holds the inline timer ────────────────
        val (rowImport, importRightSlot) = makeIconRow("›", "Import Blocklist") { importBlocklist() }

        // Timer text — INVISIBLE (not GONE) so the row height stays stable
        tvImportCountdown = TextView(this).apply {
            text = "00:00:00"
            textSize = 15f
            setTextColor(colorTimerText)
            setTypeface(null, Typeface.BOLD)
            includeFontPadding = false
            gravity = Gravity.CENTER_VERTICAL
            visibility = View.INVISIBLE
            layoutParams = FrameLayout.LayoutParams(
                ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT,
                Gravity.CENTER_VERTICAL
            )
        }
        btnImportCancel = Button(this) // inert placeholder to satisfy the lateinit field
        importRightSlot.addView(tvImportCountdown)

        // ── Exit row — icon slot fixed to iconSlotWidth so "Exit" aligns with other labels ──
        val exitIconSlot = FrameLayout(this).apply {
            layoutParams = LinearLayout.LayoutParams(iconSlotWidth, ViewGroup.LayoutParams.WRAP_CONTENT)
        }
        val exitIcon = VectorIconView(this, IconGlyph.CLOSE, Color.parseColor("#C0C0C5")).apply {
            layoutParams = FrameLayout.LayoutParams(dp(22), dp(22), Gravity.CENTER)
        }
        exitIconSlot.addView(exitIcon)
        val tvExitLabel = TextView(this).apply {
            text = "Exit"
            textSize = 17.3f
            setTextColor(rowTextColor)
        }
        val rowExit = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            gravity = Gravity.CENTER_VERTICAL
            setPadding(0, exitPadV, 0, exitPadV)
            isClickable = true
            isFocusable = true
            addView(exitIconSlot)
            addView(tvExitLabel)
            setOnClickListener { finishAffinity() }
        }

        settingsCard.addView(rowExport)
        settingsCard.addView(divider())
        settingsCard.addView(rowImport)
        settingsCard.addView(divider())
        settingsCard.addView(rowExit)
        settingsCard.addView(divider())

        mainContainer.addView(settingsCard)

        scrollView.addView(mainContainer)
        return scrollView
    }

    // =========================================================================================
    // Export / Import
    // =========================================================================================

    private fun exportBlocklist() {
        val intent = Intent(Intent.ACTION_CREATE_DOCUMENT).apply {
            addCategory(Intent.CATEGORY_OPENABLE)
            type = "application/json"
            putExtra(Intent.EXTRA_TITLE, "contentshield_blocklist.json")
        }
        startActivityForResult(intent, REQUEST_EXPORT_BLOCKLIST)
    }

    private fun importBlocklist() {
        val intent = Intent(Intent.ACTION_OPEN_DOCUMENT).apply {
            addCategory(Intent.CATEGORY_OPENABLE)
            type = "*/*"
        }
        startActivityForResult(intent, REQUEST_IMPORT_BLOCKLIST)
    }

    override fun onActivityResult(requestCode: Int, resultCode: Int, data: Intent?) {
        super.onActivityResult(requestCode, resultCode, data)
        if (resultCode != Activity.RESULT_OK) return
        val uri = data?.data ?: return
        when (requestCode) {
            REQUEST_EXPORT_BLOCKLIST -> performExport(uri)
            REQUEST_IMPORT_BLOCKLIST -> performImport(uri)
        }
    }

    private fun performExport(uri: Uri) {
        try {
            val packages = prefs.getStringSet("blocked_packages", emptySet()) ?: emptySet()
            val urls     = prefs.getStringSet("blocked_urls",     emptySet()) ?: emptySet()

            val json = JSONObject().apply {
                put("version", 1)
                put("blocked_packages", JSONArray(packages.toList()))
                put("blocked_urls",     JSONArray(urls.toList()))
            }

            contentResolver.openOutputStream(uri)?.use { out ->
                OutputStreamWriter(out, Charsets.UTF_8).use { it.write(json.toString(2)) }
            }

            val d = themedDialogBuilder()
                .setView(themedDialogContent(
                    "Export successful",
                    "Saved ${packages.size} app(s) and ${urls.size} URL(s)."
                ))
                .setPositiveButton("OK", null).create()
            applyDialogTheme(d); d.show()

        } catch (e: Exception) {
            val d = themedDialogBuilder()
                .setView(themedDialogContent("Export failed", e.localizedMessage ?: "Unknown error"))
                .setPositiveButton("OK", null).create()
            applyDialogTheme(d); d.show()
        }
    }

    private fun performImport(uri: Uri) {
        try {
            val text = contentResolver.openInputStream(uri)?.use { inp ->
                BufferedReader(InputStreamReader(inp, Charsets.UTF_8)).readText()
            } ?: throw Exception("Could not read file")

            val json     = JSONObject(text)
            val pkgArray = json.optJSONArray("blocked_packages") ?: JSONArray()
            val urlArray = json.optJSONArray("blocked_urls")     ?: JSONArray()

            val newPackages = (0 until pkgArray.length()).map { pkgArray.getString(it) }.toSet()
            val newUrls     = (0 until urlArray.length()).map { urlArray.getString(it) }.toSet()

            if (newPackages.isEmpty() && newUrls.isEmpty()) {
                val d = themedDialogBuilder()
                    .setView(themedDialogContent("Nothing to import", "The file contained no blocked apps or URLs."))
                    .setPositiveButton("OK", null).create()
                applyDialogTheme(d); d.show()
                return
            }

            // Preview dialog before starting countdown
            val summary = buildString {
                if (newPackages.isNotEmpty()) append("${newPackages.size} app(s)")
                if (newPackages.isNotEmpty() && newUrls.isNotEmpty()) append(" and ")
                if (newUrls.isNotEmpty()) append("${newUrls.size} URL(s)")
            }

            val d = themedDialogBuilder()
                .setView(themedDialogContent(
                    "Import blocklist?",
                    "This will add $summary to your blocklists."
                ))
                .setPositiveButton("Import") { _, _ ->
                    startImportCountdown(newPackages, newUrls)
                }
                .setNegativeButton("Cancel", null).create()
            applyDialogTheme(d); d.show()

        } catch (e: Exception) {
            val d = themedDialogBuilder()
                .setView(themedDialogContent("Import failed", "Could not read the file: ${e.localizedMessage}"))
                .setPositiveButton("OK", null).create()
            applyDialogTheme(d); d.show()
        }
    }

    private fun startImportCountdown(packages: Set<String>, urls: Set<String>) {
        importPendingPackages = packages
        importPendingUrls     = urls

        val delayMinutes = prefs.getInt("saved_delay_minutes", 30)

        // Show the inline timer on the Import row
        tvImportCountdown.visibility = VISIBLE

        // Switch to settings tab so the row is visible
        switchTab(Tab.SETTINGS)

        if (delayMinutes <= 0) {
            // No delay: show 00:00:00 and auto-apply immediately
            tvImportCountdown.text = "00:00:00"
            importCountdownEndTime = SystemClock.elapsedRealtime()
            applyImport()
        } else {
            val totalMs = delayMinutes * 60 * 1000L
            importCountdownEndTime = SystemClock.elapsedRealtime() + totalMs

            // Show initial time immediately
            val h = (totalMs / 3_600_000) % 24
            val m = (totalMs / 60_000)    % 60
            val s = (totalMs / 1_000)     % 60
            tvImportCountdown.text = String.format(Locale.US, "%02d:%02d:%02d", h, m, s)

            // Kick off the per-second ticker
            importCountdownHandler = Handler(Looper.getMainLooper())
            importCountdownRunnable = object : Runnable {
                override fun run() {
                    val remaining = importCountdownEndTime - SystemClock.elapsedRealtime()
                    if (remaining <= 0) {
                        tvImportCountdown.text = "00:00:00"
                        tvImportCountdown.setOnClickListener {
                            val d = themedDialogBuilder()
                                .setView(themedDialogContent(
                                    "Apply import?",
                                    "Import the blocklist now?"
                                ))
                                .setPositiveButton("Confirm") { _, _ -> applyImport() }
                                .setNegativeButton("Cancel") { _, _ -> cancelImportCountdown() }
                                .create()
                            applyDialogTheme(d); d.show()
                        }
                    } else {
                        val rh = (remaining / 3_600_000) % 24
                        val rm = (remaining / 60_000)    % 60
                        val rs = (remaining / 1_000)     % 60
                        tvImportCountdown.text = String.format(Locale.US, "%02d:%02d:%02d", rh, rm, rs)
                        tvImportCountdown.setOnClickListener {
                            showResetTimerDialog {
                                cancelImportCountdown()
                            }
                        }
                        importCountdownHandler?.postDelayed(this, 1000)
                    }
                }
            }
            importCountdownHandler?.post(importCountdownRunnable!!)
        }
    }

    private fun cancelImportCountdown() {
        importCountdownRunnable?.let { importCountdownHandler?.removeCallbacks(it) }
        importCountdownRunnable  = null
        importCountdownHandler   = null
        importPendingPackages    = emptySet()
        importPendingUrls        = emptySet()
        // Hide inline timer, restore row to idle state
        tvImportCountdown.visibility = View.INVISIBLE
    }

    private fun applyImport() {
        importCountdownRunnable?.let { importCountdownHandler?.removeCallbacks(it) }
        importCountdownRunnable = null
        importCountdownHandler  = null

        val isDeviceOwner = dpm.isDeviceOwnerApp(packageName)

        // Merge packages
        if (importPendingPackages.isNotEmpty()) {
            val current = prefs.getStringSet("blocked_packages", emptySet())?.toMutableSet() ?: mutableSetOf()
            current.addAll(importPendingPackages)
            prefs.edit().putStringSet("blocked_packages", current).apply()
            if (isDeviceOwner) {
                importPendingPackages.forEach { pkg ->
                    if (pkg == packageName) return@forEach
                    try { dpm.setPackagesSuspended(adminComponent, arrayOf(pkg), true) } catch (_: Exception) {}
                }
            }
            refreshBlockedAppsList(isDeviceOwner)
        }

        // Merge URLs
        if (importPendingUrls.isNotEmpty()) {
            val current = prefs.getStringSet("blocked_urls", emptySet())?.toMutableSet() ?: mutableSetOf()
            current.addAll(importPendingUrls.map { it.lowercase() })
            prefs.edit().putStringSet("blocked_urls", current).apply()
            refreshBlockedUrlsList()
        }

        importPendingPackages        = emptySet()
        importPendingUrls            = emptySet()
        tvImportCountdown.visibility = View.INVISIBLE

        val d = themedDialogBuilder()
            .setView(themedDialogContent("Import complete", "Blocklists have been updated."))
            .setPositiveButton("OK", null).create()
        applyDialogTheme(d); d.show()
    }

    // =========================================================================================
    // Lifecycle
    // =========================================================================================

    override fun onResume() {
        super.onResume()
        // Catches the case where a blocked app was reinstalled while ContentShield wasn't
        // running at all (so the PACKAGE_ADDED broadcast, even if delivered, had no one to
        // notify) or while its delivery was deferred by the OS.
        resyncBlockedPackages(dpm.isDeviceOwnerApp(packageName))
        // Catches the common flow of tapping the warning card, enabling the service in
        // Settings, then pressing Back to return here.
        updateAccessibilityWarningUI()
    }

    private fun isAccessibilityServiceEnabled(): Boolean {
        val expectedComponent = ComponentName(this, BlockerAccessibilityService::class.java)
        val enabledServicesSetting = Settings.Secure.getString(
            contentResolver,
            Settings.Secure.ENABLED_ACCESSIBILITY_SERVICES
        ) ?: return false

        val splitter = TextUtils.SimpleStringSplitter(':')
        splitter.setString(enabledServicesSetting)
        while (splitter.hasNext()) {
            val enabledService = ComponentName.unflattenFromString(splitter.next())
            if (enabledService != null && enabledService == expectedComponent) return true
        }
        return false
    }

    // Deep-links straight to the "on/off" toggle screen for BlockerAccessibilityService.
    // On API 34+, the accessibility-details-settings screen + component-name extra opens
    // that exact screen. These are referenced by literal string rather than the
    // Settings.ACTION_ACCESSIBILITY_DETAILS_SETTINGS / EXTRA_ACCESSIBILITY_SERVICE_COMPONENT_NAME
    // constants because those aren't present in SDK stubs below compileSdk 34 - using the
    // literal values means this still compiles regardless of this project's compileSdk, and
    // simply falls through to the generic list at runtime on devices below API 34.
    // On older versions there's no reliable public API for that, so fall back
    // to the general accessibility services list.
    private fun openAccessibilityServiceSettings() {
        val expectedComponent = ComponentName(this, BlockerAccessibilityService::class.java)
        if (Build.VERSION.SDK_INT >= 34) {
            try {
                val intent = Intent("android.settings.ACCESSIBILITY_DETAILS_SETTINGS").apply {
                    putExtra("android.provider.extra.COMPONENT_NAME", expectedComponent.flattenToString())
                }
                startActivity(intent)
                return
            } catch (e: Exception) {
                // Fall through to the generic list below.
            }
        }
        startActivity(Intent(Settings.ACTION_ACCESSIBILITY_SETTINGS))
    }

    private fun updateAccessibilityWarningUI() {
        accessibilityWarningCard.visibility = if (isAccessibilityServiceEnabled()) GONE else VISIBLE
    }

    private fun resyncBlockedPackages(isDeviceOwner: Boolean) {
        if (!isDeviceOwner) return
        val blockedSet = prefs.getStringSet("blocked_packages", emptySet()) ?: emptySet()
        for (pkg in blockedSet) {
            try {
                // No-op if already suspended; actually applies it if the package just
                // became installed again (e.g. reinstalled) since we last checked.
                dpm.setPackagesSuspended(adminComponent, arrayOf(pkg), true)
            } catch (e: Exception) {
                // Package genuinely not installed yet - nothing to do until it is.
                e.printStackTrace()
            }
        }
    }

    private fun suspendPackage(pkgName: String) {
        if (pkgName == packageName) return
        val currentBlocked = prefs.getStringSet("blocked_packages", emptySet())?.toMutableSet() ?: mutableSetOf()
        currentBlocked.add(pkgName)
        prefs.edit().putStringSet("blocked_packages", currentBlocked).apply()

        try {
            dpm.setPackagesSuspended(adminComponent, arrayOf(pkgName), true)
        } catch (e: Exception) {
            e.printStackTrace()
        }
        refreshBlockedAppsList(dpm.isDeviceOwnerApp(packageName))
    }

    private fun unsuspendPackage(pkgName: String) {
        val currentBlocked = prefs.getStringSet("blocked_packages", emptySet())?.toMutableSet() ?: mutableSetOf()
        currentBlocked.remove(pkgName)
        prefs.edit().putStringSet("blocked_packages", currentBlocked).apply()

        try {
            dpm.setPackagesSuspended(adminComponent, arrayOf(pkgName), false)
        } catch (e: Exception) {
            e.printStackTrace()
        }
        refreshBlockedAppsList(dpm.isDeviceOwnerApp(packageName))
    }

    private fun refreshBlockedAppsList(isDeviceOwner: Boolean) {
        blockedAppsListContainer.removeAllViews()
        blockedAppRowViews.clear()
        val blockedSet = prefs.getStringSet("blocked_packages", emptySet()) ?: emptySet()

        tvBlocklistEmpty.visibility = if (blockedSet.isEmpty()) VISIBLE else GONE
        blockedAppsScroll.visibility = if (blockedSet.isEmpty()) GONE else VISIBLE

        if (blockedSet.isEmpty()) return

        blockedSet.forEach { pkg ->
            val row = LinearLayout(this).apply {
                orientation = LinearLayout.VERTICAL
                setPadding(dp(14), dp(14), dp(14), dp(14))
                val bg = GradientDrawable().apply {
                    setColor(colorCard)
                    cornerRadius = dp(10).toFloat()
                }
                background = bg
                layoutParams = LinearLayout.LayoutParams(
                    ViewGroup.LayoutParams.MATCH_PARENT,
                    ViewGroup.LayoutParams.WRAP_CONTENT
                ).apply { topMargin = dp(8) }
            }

            val topRow = LinearLayout(this).apply {
                orientation = LinearLayout.HORIZONTAL
                gravity = Gravity.CENTER_VERTICAL
                layoutParams = LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT)
            }

            val tvPkgName = TextView(this).apply {
                text = pkg
                textSize = 16f
                setTextColor(Color.WHITE)
                maxLines = 1
                ellipsize = android.text.TextUtils.TruncateAt.END
                includeFontPadding = false
                gravity = Gravity.CENTER_VERTICAL
                setPadding(0, dp(6), 0, dp(6))
                layoutParams = LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f).apply {
                    marginEnd = dp(10)
                    topMargin = 6
                }
            }

            val btnUnblock = TextView(this).apply {
                text = "✕"
                setTextColor(colorAccentRed)
                textSize = 14f
                setTypeface(null, Typeface.BOLD)
                includeFontPadding = false
                gravity = Gravity.CENTER
                background = GradientDrawable().apply {
                    shape = GradientDrawable.OVAL
                    setColor(colorAccentRedDark)
                }
                layoutParams = LinearLayout.LayoutParams(dp(28), dp(28)).apply {
                    topMargin = 6
                }
            }

            val tvStatus = TextView(this).apply {
                text = ""
                textSize = 11.9f
                setTextColor(colorAmber)
                setPadding(0, dp(8), 0, 0)
                visibility = GONE
            }

            val actionRow = LinearLayout(this).apply {
                orientation = LinearLayout.HORIZONTAL
                layoutParams = LinearLayout.LayoutParams(ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT).apply { topMargin = dp(8) }
            }

            val btnCancel = Button(this).apply {
                text = "Cancel"
                textSize = 10.8f
                setTextColor(colorAccentRed)
                setTypeface(null, Typeface.BOLD)
                val bg = GradientDrawable().apply {
                    setColor(colorAccentRedDark)
                    cornerRadius = dp(6).toFloat()
                }
                background = bg
                setPadding(dp(8), dp(2), dp(8), dp(2))
                visibility = GONE
                layoutParams = LinearLayout.LayoutParams(ViewGroup.LayoutParams.WRAP_CONTENT, dp(30))
            }

            val btnApply = Button(this).apply {
                text = "Confirm"
                textSize = 10.8f
                setTextColor(colorGreen)
                setTypeface(null, Typeface.BOLD)
                val bg = GradientDrawable().apply {
                    setColor(Color.parseColor("#1B2E1E"))
                    cornerRadius = dp(6).toFloat()
                }
                background = bg
                setPadding(dp(8), dp(2), dp(8), dp(2))
                visibility = GONE
                layoutParams = LinearLayout.LayoutParams(ViewGroup.LayoutParams.WRAP_CONTENT, dp(30)).apply { marginStart = dp(8) }
            }

            actionRow.addView(btnCancel)
            actionRow.addView(btnApply)

            val tvCountdown = TextView(this).apply {
                text = ""
                textSize = 14f
                setTextColor(Color.WHITE)
                setTypeface(null, Typeface.BOLD)
                includeFontPadding = false
                gravity = Gravity.CENTER_VERTICAL
                visibility = GONE
                layoutParams = LinearLayout.LayoutParams(ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT).apply {
                    topMargin = 6
                    marginEnd = dp(14)
                }
            }

            blockedAppRowViews[pkg] = BlockedAppRowViews(tvStatus, btnCancel, btnApply, btnUnblock, tvCountdown)

            fun startAppCountdownTicker(endTime: Long) {
                val handler = android.os.Handler(mainLooper)
                val ticker = object : Runnable {
                    override fun run() {
                        val currentRow = blockedAppRowViews[pkg] ?: return
                        if (pkg !in inCountdownMode) return
                        val remaining = endTime - SystemClock.elapsedRealtime()
                        if (remaining <= 0) {
                            currentRow.tvCountdown.text = "00:00:00"
                            currentRow.tvCountdown.setOnClickListener { showUnblockConfirmDialog(pkg) }
                        } else {
                            val h = (remaining / 3600000).toInt()
                            val m = ((remaining % 3600000) / 60000).toInt()
                            val s = ((remaining % 60000) / 1000).toInt()
                            currentRow.tvCountdown.text = String.format(Locale.US, "%02d:%02d:%02d", h, m, s)
                            currentRow.tvCountdown.setOnClickListener {
                                showResetTimerDialog {
                                    inCountdownMode.remove(pkg)
                                    appCountdownEndTimes.remove(pkg)
                                    currentRow.tvCountdown.visibility = GONE
                                    currentRow.tvCountdown.setOnClickListener(null)
                                    blockedAppRowViews[pkg]?.btnUnblock?.visibility = VISIBLE
                                }
                            }
                            handler.postDelayed(this, 1000)
                        }
                    }
                }
                handler.post(ticker)
            }

            // Restore countdown UI if this item was already counting down before the list rebuilt
            if (pkg in inCountdownMode) {
                btnUnblock.visibility = GONE
                tvCountdown.visibility = VISIBLE
                val savedEndTime = appCountdownEndTimes[pkg]
                if (savedEndTime == null || savedEndTime <= SystemClock.elapsedRealtime()) {
                    tvCountdown.text = "00:00:00"
                    tvCountdown.setOnClickListener { showUnblockConfirmDialog(pkg) }
                } else {
                    startAppCountdownTicker(savedEndTime)
                }
            }

            btnUnblock.setOnClickListener {
                if (!checkDeviceOwner(isDeviceOwner)) return@setOnClickListener
                val activeDelayMinutes = prefs.getInt("saved_delay_minutes", 30)
                btnUnblock.visibility = GONE
                tvCountdown.visibility = VISIBLE
                inCountdownMode.add(pkg)
                if (activeDelayMinutes <= 0) {
                    appCountdownEndTimes[pkg] = SystemClock.elapsedRealtime()
                    tvCountdown.text = "00:00:00"
                    tvCountdown.setOnClickListener { showUnblockConfirmDialog(pkg) }
                } else {
                    val totalMs = activeDelayMinutes * 60 * 1000L
                    val endTime = SystemClock.elapsedRealtime() + totalMs
                    appCountdownEndTimes[pkg] = endTime
                    startAppCountdownTicker(endTime)
                }
            }

            btnCancel.setOnClickListener {
                cancelPendingUnblock(pkg)
                inCountdownMode.remove(pkg)
                appCountdownEndTimes.remove(pkg)
                tvStatus.visibility = GONE
                btnCancel.visibility = GONE
                btnApply.visibility = GONE
                tvCountdown.visibility = GONE
                btnUnblock.visibility = VISIBLE
            }

            btnApply.setOnClickListener {
                prefs.edit()
                    .putBoolean("is_pending_unblock_$pkg", false)
                    .putBoolean("is_awaiting_confirm_unblock_$pkg", false)
                    .apply()
                endVerificationAttempted.remove("unblock_$pkg")
                inCountdownMode.remove(pkg)
                appCountdownEndTimes.remove(pkg)
                unsuspendPackage(pkg)
            }

            topRow.addView(tvPkgName)
            topRow.addView(btnUnblock)
            topRow.addView(tvCountdown)
            row.addView(topRow)
            row.addView(tvStatus)
            row.addView(actionRow)
            blockedAppsListContainer.addView(row)
        }
    }

    // Shows "Do you want to reset the timer?" popup with Reset / Do nothing.
    // onReset is called if the user chooses Reset.
    private fun showResetTimerDialog(onCancel: () -> Unit) {
        val d = themedDialogBuilder()
            .setView(themedDialogContent("Abort?", "Are you sure you want to abort?"))
            .setPositiveButton("Abort") { _, _ -> onCancel() }
            .setNegativeButton("Cancel", null)
            .create()
        applyDialogTheme(d)
        d.show()
    }

    private fun initiateDelayChangeTimer(activeDelayMinutes: Int, pendingMinutes: Int) {
        endVerificationAttempted.remove("delay_change")
        awaitingInitialFetch.add("delay_change")

        // Show the full requested duration right away so the row never appears blank.
        // This is a frozen display only — awaitingInitialFetch keeps the 1s tick loop from
        // touching it until target_unlock_time_delay_change is actually written below, so
        // it won't start counting down until network time is confirmed.
        val initialDurationMs = activeDelayMinutes * 60 * 1000L
        val initHours = (initialDurationMs / (1000 * 60 * 60)) % 24
        val initMinutes = (initialDurationMs / (1000 * 60)) % 60
        val initSeconds = (initialDurationMs / 1000) % 60
        tvDelayTimerReplace.text = String.format(Locale.US, "%02d:%02d:%02d", initHours, initMinutes, initSeconds)
        tvDelayTimerReplace.setTextColor(colorTimerText)
        tvDelayTimerReplace.setOnClickListener(null)
        tvDelayTimerReplace.visibility = VISIBLE
        btnDelayEdit.visibility = GONE

        retryNetworkTimeUntilSuccess(isCancelled = { "delay_change" !in awaitingInitialFetch }) { networkTime ->
            val targetUnlockTime = networkTime + (activeDelayMinutes * 60 * 1000L)
            val currentElapsedRealtime = SystemClock.elapsedRealtime()

            prefs.edit().apply {
                putInt("pending_delay_minutes", pendingMinutes)
                putLong("target_unlock_time_delay_change", targetUnlockTime)
                putLong("lock_start_elapsed_delay_change", currentElapsedRealtime)
                putLong("lock_duration_ms_delay_change", activeDelayMinutes * 60 * 1000L)
                putBoolean("is_pending_delay_change", true)
                apply()
            }
            awaitingInitialFetch.remove("delay_change")
        }
    }

    private fun cancelPendingDelayChange() {
        endVerificationAttempted.remove("delay_change")
        awaitingInitialFetch.remove("delay_change")
        prefs.edit()
            .putBoolean("is_pending_delay_change", false)
            .putBoolean("is_awaiting_confirm_delay_change", false)
            .apply()
    }

    private fun initiateTurnOffDelay(key: String, minutes: Int, holder: OptionCardHolder) {
        endVerificationAttempted.remove(key)
        awaitingInitialFetch.add(key)

        // Show the full requested duration right away so the toggle never appears blank.
        // This is a frozen display only — awaitingInitialFetch keeps the 1s tick loop from
        // touching it until target_unlock_time_$key is actually written below, so it won't
        // start counting down until network time is confirmed.
        val initialDurationMs = minutes * 60 * 1000L
        val initHours = (initialDurationMs / (1000 * 60 * 60)) % 24
        val initMinutes = (initialDurationMs / (1000 * 60)) % 60
        val initSeconds = (initialDurationMs / 1000) % 60
        // Replace the toggle switch with a timer display (no bottom status row)
        holder.switch.visibility = View.INVISIBLE
        holder.tvTimerReplace?.text = String.format(Locale.US, "%02d:%02d:%02d", initHours, initMinutes, initSeconds)
        holder.tvTimerReplace?.setTextColor(colorTimerText)
        holder.tvTimerReplace?.setOnClickListener(null)
        holder.tvTimerReplace?.visibility = VISIBLE

        retryNetworkTimeUntilSuccess(isCancelled = { key !in awaitingInitialFetch }) { networkTime ->
            val targetUnlockTime = networkTime + (minutes * 60 * 1000L)
            val currentElapsedRealtime = SystemClock.elapsedRealtime()

            prefs.edit().apply {
                putLong("target_unlock_time_$key", targetUnlockTime)
                putLong("lock_start_elapsed_$key", currentElapsedRealtime)
                putLong("lock_duration_ms_$key", minutes * 60 * 1000L)
                putBoolean("is_pending_off_$key", true)
                apply()
            }
            awaitingInitialFetch.remove(key)
        }
    }

    private fun cancelPendingOff(key: String) {
        endVerificationAttempted.remove(key)
        awaitingInitialFetch.remove(key)
        prefs.edit()
            .putBoolean("is_pending_off_$key", false)
            .putBoolean("is_awaiting_confirm_off_$key", false)
            .apply()
    }

    private fun initiateUnblockDelay(pkg: String, minutes: Int) {
        val row = blockedAppRowViews[pkg] ?: return
        val verifyKey = "unblock_$pkg"
        endVerificationAttempted.remove(verifyKey)
        awaitingInitialFetch.add(verifyKey)

        // Show the full requested duration right away so the toggle never appears blank.
        // This is a frozen display only — awaitingInitialFetch keeps the 1s tick loop from
        // touching it until target_unlock_time_unblock_$pkg is actually written below, so it
        // won't start counting down until network time is confirmed.
        val initialDurationMs = minutes * 60 * 1000L
        val initHours = (initialDurationMs / (1000 * 60 * 60)) % 24
        val initMinutes = (initialDurationMs / (1000 * 60)) % 60
        val initSeconds = (initialDurationMs / 1000) % 60
        row.tvStatus.text = String.format(Locale.US, "%02d:%02d:%02d", initHours, initMinutes, initSeconds)
        row.tvStatus.setTextColor(colorTimerText)
        row.tvStatus.setOnClickListener(null)
        row.tvStatus.visibility = VISIBLE
        row.btnCancel.visibility = VISIBLE
        row.btnApply.visibility = GONE
        row.btnUnblock.visibility = GONE

        retryNetworkTimeUntilSuccess(isCancelled = { verifyKey !in awaitingInitialFetch }) { networkTime ->
            val targetUnlockTime = networkTime + (minutes * 60 * 1000L)
            val currentElapsedRealtime = SystemClock.elapsedRealtime()

            prefs.edit().apply {
                putLong("target_unlock_time_unblock_$pkg", targetUnlockTime)
                putLong("lock_start_elapsed_unblock_$pkg", currentElapsedRealtime)
                putLong("lock_duration_ms_unblock_$pkg", minutes * 60 * 1000L)
                putBoolean("is_pending_unblock_$pkg", true)
                apply()
            }
            awaitingInitialFetch.remove(verifyKey)
        }
    }

    private fun cancelPendingUnblock(pkg: String) {
        val verifyKey = "unblock_$pkg"
        endVerificationAttempted.remove(verifyKey)
        awaitingInitialFetch.remove(verifyKey)
        prefs.edit()
            .putBoolean("is_pending_unblock_$pkg", false)
            .putBoolean("is_awaiting_confirm_unblock_$pkg", false)
            .apply()
    }

    private fun startTimerLoop() {
        timerRunnable = object : Runnable {
            override fun run() {
                updateDelayCardUI()
                updateAllCardsUI()
                updateBlockedAppsUI()
                updateBlockedUrlsUI()
                handler.postDelayed(this, 1000)
            }
        }
        handler.post(timerRunnable!!)
    }

    private fun updateDelayCardUI() {
        val isAwaitingConfirm = prefs.getBoolean("is_awaiting_confirm_delay_change", false)
        val isPendingDelayChange = prefs.getBoolean("is_pending_delay_change", false)

        if (isAwaitingConfirm) {
            // Countdown complete — show tappable 00:00:00 timer (same pattern as toggle rows)
            tvDelayTimerReplace.text = "00:00:00"
            tvDelayTimerReplace.setTextColor(colorTimerText)
            tvDelayTimerReplace.visibility = VISIBLE
            btnDelayEdit.visibility = GONE
            if (tvDelayTimerReplace.tag != "confirm_delay_change") {
                tvDelayTimerReplace.tag = "confirm_delay_change"
                tvDelayTimerReplace.setOnClickListener {
                    val pendingMinutes = prefs.getInt("pending_delay_minutes", 0)
                    val d = themedDialogBuilder()
                        .setView(themedDialogContent(
                            "Apply delay change?",
                            "Change the delay to $pendingMinutes minutes?"
                        ))
                        .setPositiveButton("Confirm") { _, _ ->
                            prefs.edit().apply {
                                putInt("saved_delay_minutes", pendingMinutes)
                                putBoolean("is_pending_delay_change", false)
                                putBoolean("is_awaiting_confirm_delay_change", false)
                                apply()
                            }
                            endVerificationAttempted.remove("delay_change")
                            tvDelayValue.text = "$pendingMinutes minutes"
                            tvDelayTimerReplace.tag = null
                            tvDelayTimerReplace.visibility = GONE
                            btnDelayEdit.visibility = VISIBLE
                        }
                        .setNegativeButton("Cancel") { _, _ ->
                            cancelPendingDelayChange()
                            tvDelayTimerReplace.tag = null
                            tvDelayTimerReplace.visibility = GONE
                            btnDelayEdit.visibility = VISIBLE
                        }
                        .create()
                    applyDialogTheme(d)
                    d.show()
                }
            }
            return
        }

        if (!isPendingDelayChange) {
            if ("delay_change" !in awaitingInitialFetch) {
                tvDelayTimerReplace.tag = null
                tvDelayTimerReplace.visibility = GONE
                btnDelayEdit.visibility = VISIBLE
            }
            return
        }

        tvDelayTimerReplace.visibility = VISIBLE
        btnDelayEdit.visibility = GONE
        val targetUnlockTime = prefs.getLong("target_unlock_time_delay_change", 0L)
        val lockStartElapsed = prefs.getLong("lock_start_elapsed_delay_change", 0L)
        val durationMs = prefs.getLong("lock_duration_ms_delay_change", 0L)

        val elapsedSinceLock = SystemClock.elapsedRealtime() - lockStartElapsed

        if (elapsedSinceLock < durationMs) {
            val remainingMs = durationMs - elapsedSinceLock
            val hours = (remainingMs / (1000 * 60 * 60)) % 24
            val minutes = (remainingMs / (1000 * 60)) % 60
            val seconds = (remainingMs / 1000) % 60

            tvDelayTimerReplace.text = String.format(Locale.US, "%02d:%02d:%02d", hours, minutes, seconds)
            tvDelayTimerReplace.setTextColor(colorTimerText)
            tvDelayTimerReplace.setOnClickListener {
                showResetTimerDialog {
                    cancelPendingDelayChange()
                    tvDelayTimerReplace.tag = null
                    tvDelayTimerReplace.visibility = GONE
                    btnDelayEdit.visibility = VISIBLE
                }
            }
        } else {
            // Countdown reached zero: verify against network time, retrying silently in the
            // background until confirmed (see verifyNetworkTimeReached).
            if ("delay_change" in endVerificationAttempted) return

            if (tvDelayTimerReplace.text != "00:00:00") {
                tvDelayTimerReplace.text = "00:00:00"
                tvDelayTimerReplace.setTextColor(colorTimerText)
            }
            endVerificationAttempted.add("delay_change")

            verifyNetworkTimeReached(targetUnlockTime, isCancelled = { "delay_change" !in endVerificationAttempted }) {
                prefs.edit()
                    .putBoolean("is_pending_delay_change", false)
                    .putBoolean("is_awaiting_confirm_delay_change", true)
                    .apply()
            }
        }
    }

    private fun updateAllCardsUI() {
        cardViews.forEach { (key, holder) ->
            val isAwaitingConfirm = prefs.getBoolean("is_awaiting_confirm_off_$key", false)
            val isPendingOff = prefs.getBoolean("is_pending_off_$key", false)

            if (isAwaitingConfirm) {
                // Network confirmed the delay elapsed. Keep the 00:00:00 timer visible and
                // clickable. Must set the click listener here explicitly — after an app
                // restart all views are freshly created with no listener attached.
                holder.switch.visibility = View.INVISIBLE
                holder.tvTimerReplace?.visibility = VISIBLE
                holder.tvTimerReplace?.text = "00:00:00"
                holder.tvTimerReplace?.setTextColor(colorTimerText)
                // Guard with a tag so we don't re-set the same listener every 1s tick
                if (holder.tvTimerReplace?.tag != "confirm_$key") {
                    holder.tvTimerReplace?.tag = "confirm_$key"
                    holder.tvTimerReplace?.setOnClickListener {
                        val d = themedDialogBuilder()
                            .setView(themedDialogContent(
                                "Turn off?",
                                "Are you sure you want to turn this off?"
                            ))
                            .setPositiveButton("Confirm") { _, _ ->
                                prefs.edit()
                                    .putBoolean("is_pending_off_$key", false)
                                    .putBoolean("is_awaiting_confirm_off_$key", false)
                                    .apply()
                                endVerificationAttempted.remove(key)
                                try {
                                    holder.disableRestriction()
                                    holder.tvTimerReplace?.tag = null
                                    holder.tvTimerReplace?.visibility = View.INVISIBLE
                                    holder.switch.visibility = VISIBLE
                                    holder.switch.isChecked = false
                                } catch (e: Exception) { /* ignore */ }
                            }
                            .setNegativeButton("Cancel") { _, _ ->
                                cancelPendingOff(key)
                                holder.tvTimerReplace?.tag = null
                                holder.tvTimerReplace?.visibility = View.INVISIBLE
                                holder.switch.visibility = VISIBLE
                            }
                            .create()
                        applyDialogTheme(d)
                        d.show()
                    }
                }
                return@forEach
            }

            if (!isPendingOff) {
                if (key !in awaitingInitialFetch) {
                    // Restore switch visibility when no longer pending
                    holder.tvTimerReplace?.visibility = View.INVISIBLE
                    holder.switch.visibility = VISIBLE
                }
                return@forEach
            }

            // Keep switch hidden and timer visible while pending
            holder.switch.visibility = View.INVISIBLE
            holder.tvTimerReplace?.visibility = VISIBLE
            val targetUnlockTime = prefs.getLong("target_unlock_time_$key", 0L)
            val lockStartElapsed = prefs.getLong("lock_start_elapsed_$key", 0L)
            val durationMs = prefs.getLong("lock_duration_ms_$key", 0L)

            val elapsedSinceLock = SystemClock.elapsedRealtime() - lockStartElapsed

            if (elapsedSinceLock < durationMs) {
                val remainingMs = durationMs - elapsedSinceLock
                val hours = (remainingMs / (1000 * 60 * 60)) % 24
                val minutes = (remainingMs / (1000 * 60)) % 60
                val seconds = (remainingMs / 1000) % 60

                val timeStr = String.format(Locale.US, "%02d:%02d:%02d", hours, minutes, seconds)
                holder.tvTimerReplace?.text = timeStr
                holder.tvTimerReplace?.setTextColor(colorTimerText)
                holder.tvTimerReplace?.setOnClickListener {
                    showResetTimerDialog {
                        cancelPendingOff(key)
                        holder.tvTimerReplace?.tag = null
                        holder.tvTimerReplace?.visibility = View.INVISIBLE
                        holder.switch.visibility = VISIBLE
                    }
                }
            } else {
                // Countdown reached zero: verify against network time, retrying silently in
                // the background until confirmed (see verifyNetworkTimeReached).
                if (key in endVerificationAttempted) return@forEach

                if (holder.tvTimerReplace?.text != "00:00:00") {
                    holder.tvTimerReplace?.text = "00:00:00"
                    holder.tvTimerReplace?.setTextColor(colorTimerText)
                }
                // When timer hits zero, tapping it shows an untoggle confirmation popup
                holder.tvTimerReplace?.setOnClickListener {
                    val d = themedDialogBuilder()
                        .setView(themedDialogContent(
                            "Turn off?",
                            "Are you sure you want to turn this off?"
                        ))
                        .setPositiveButton("Confirm") { _, _ ->
                            prefs.edit()
                                .putBoolean("is_pending_off_$key", false)
                                .putBoolean("is_awaiting_confirm_off_$key", false)
                                .apply()
                            endVerificationAttempted.remove(key)
                            try {
                                holder.disableRestriction()
                                holder.tvTimerReplace?.visibility = View.INVISIBLE
                                holder.switch.visibility = VISIBLE
                                holder.switch.isChecked = false
                            } catch (e: Exception) { /* ignore */ }
                        }
                        .setNegativeButton("Cancel") { _, _ ->
                            // Cancel: abort the pending off and restore the toggle switch
                            cancelPendingOff(key)
                            holder.tvTimerReplace?.visibility = View.INVISIBLE
                            holder.switch.visibility = VISIBLE
                        }
                        .create()
                    applyDialogTheme(d)
                    d.show()
                }
                endVerificationAttempted.add(key)

                verifyNetworkTimeReached(targetUnlockTime, isCancelled = { key !in endVerificationAttempted }) {
                    prefs.edit()
                        .putBoolean("is_pending_off_$key", false)
                        .putBoolean("is_awaiting_confirm_off_$key", true)
                        .apply()
                }
            }
        }
    }

    private fun updateBlockedAppsUI() {
        val blockedSet = prefs.getStringSet("blocked_packages", emptySet()) ?: emptySet()

        blockedSet.toList().forEach { pkg ->
            val row = blockedAppRowViews[pkg] ?: return@forEach
            val verifyKey = "unblock_$pkg"
            val isAwaitingConfirm = prefs.getBoolean("is_awaiting_confirm_$verifyKey", false)
            val isPendingUnblock = prefs.getBoolean("is_pending_unblock_$pkg", false)

            if (isAwaitingConfirm) {
                row.tvStatus.text = "00h 00m 00s"
                row.tvStatus.setTextColor(colorTimerText)
                row.tvStatus.visibility = VISIBLE
                row.btnUnblock.visibility = GONE
                row.btnCancel.visibility = VISIBLE
                row.btnApply.visibility = VISIBLE
                return@forEach
            }
            row.btnApply.visibility = GONE

            if (!isPendingUnblock) {
                if (verifyKey !in awaitingInitialFetch && pkg !in inCountdownMode) {
                    row.tvStatus.visibility = GONE
                    row.btnCancel.visibility = GONE
                    row.btnUnblock.visibility = VISIBLE
                }
                return@forEach
            }

            row.tvStatus.visibility = VISIBLE
            row.btnCancel.visibility = VISIBLE
            row.btnUnblock.visibility = GONE

            val targetUnlockTime = prefs.getLong("target_unlock_time_unblock_$pkg", 0L)
            val lockStartElapsed = prefs.getLong("lock_start_elapsed_unblock_$pkg", 0L)
            val durationMs = prefs.getLong("lock_duration_ms_unblock_$pkg", 0L)

            val elapsedSinceLock = SystemClock.elapsedRealtime() - lockStartElapsed

            if (elapsedSinceLock < durationMs) {
                val remainingMs = durationMs - elapsedSinceLock
                val hours = (remainingMs / (1000 * 60 * 60)) % 24
                val minutes = (remainingMs / (1000 * 60)) % 60
                val seconds = (remainingMs / 1000) % 60

                row.tvStatus.text = String.format(Locale.US, "%02d:%02d:%02d", hours, minutes, seconds)
                row.tvStatus.setTextColor(colorTimerText)
                row.tvStatus.setOnClickListener(null)
            } else {
                // Countdown reached zero: verify against network time, retrying silently in
                // the background until confirmed (see verifyNetworkTimeReached).
                if (verifyKey in endVerificationAttempted) return@forEach

                if (row.tvStatus.text != "00h 00m 00s") {
                    row.tvStatus.text = "00h 00m 00s"
                    row.tvStatus.setTextColor(colorTimerText)
                }
                endVerificationAttempted.add(verifyKey)

                verifyNetworkTimeReached(targetUnlockTime, isCancelled = { verifyKey !in endVerificationAttempted }) {
                    prefs.edit()
                        .putBoolean("is_pending_unblock_$pkg", false)
                        .putBoolean("is_awaiting_confirm_$verifyKey", true)
                        .apply()
                }
            }
        }
    }

    // Each *UI() function above fires at most one network-time verification attempt per
    // pending item, right when its countdown reaches zero (tracked via
    // endVerificationAttempted), instead of re-fetching on every 1s tick.

    // Keeps calling getNetworkTime in the background until it succeeds, silently — no error
    // text, no tap-to-retry. isCancelled is checked before firing and again when the result
    // lands, so cancelling the pending action (turn off / unblock / delay change) stops the
    // retry loop instead of it firing stale writes into prefs later.
    private fun retryNetworkTimeUntilSuccess(delayMs: Long = 3000L, isCancelled: () -> Boolean = { false }, onSuccess: (Long) -> Unit) {
        if (isCancelled()) return
        getNetworkTime { networkTime ->
            runOnUiThread {
                if (isCancelled()) return@runOnUiThread
                if (networkTime != null) {
                    onSuccess(networkTime)
                } else {
                    handler.postDelayed({ retryNetworkTimeUntilSuccess(delayMs, isCancelled, onSuccess) }, delayMs)
                }
            }
        }
    }

    // Same idea, but for the end-of-countdown check: keeps retrying silently until network
    // time actually reaches targetUnlockTime (covers both no-connection and clock-tampering
    // cases identically — just keep waiting, no message shown).
    private fun verifyNetworkTimeReached(targetUnlockTime: Long, delayMs: Long = 3000L, isCancelled: () -> Boolean = { false }, onConfirmed: () -> Unit) {
        if (isCancelled()) return
        getNetworkTime { networkTime ->
            runOnUiThread {
                if (isCancelled()) return@runOnUiThread
                if (networkTime != null && networkTime >= targetUnlockTime) {
                    onConfirmed()
                } else {
                    handler.postDelayed({ verifyNetworkTimeReached(targetUnlockTime, delayMs, isCancelled, onConfirmed) }, delayMs)
                }
            }
        }
    }

    private fun getNetworkTime(callback: (Long?) -> Unit) {
        Thread {
            try {
                val url = URL("https://www.google.com")
                val connection = url.openConnection() as HttpURLConnection
                connection.connectTimeout = 3000
                connection.readTimeout = 3000
                connection.requestMethod = "HEAD"
                val dateHeader = connection.getHeaderField("Date")
                connection.disconnect()

                if (dateHeader != null) {
                    val format = SimpleDateFormat("EEE, dd MMM yyyy HH:mm:ss z", Locale.US)
                    val date = format.parse(dateHeader)
                    callback(date?.time)
                } else {
                    callback(null)
                }
            } catch (e: Exception) {
                callback(null)
            }
        }.start()
    }

    private fun checkDeviceOwner(isDeviceOwner: Boolean): Boolean {
        return isDeviceOwner
    }


    // ═══════════════════════════════════════════════════════════════════════
    // URL blocklist helpers
    // ═══════════════════════════════════════════════════════════════════════

    private fun showAddUrlDialog() {
        val container = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            setPadding(dp(24), dp(16), dp(24), dp(20))
        }
        val etUrl = EditText(this).apply {
            hint = "example.com/path"
            setTextColor(Color.WHITE)
            setHintTextColor(Color.GRAY)
            inputType = android.text.InputType.TYPE_CLASS_TEXT or
                    android.text.InputType.TYPE_TEXT_VARIATION_URI
        }
        container.addView(etUrl)

        val dialog = themedDialogBuilder()
            .setView(themedDialogContent("Block a website", extra = container))
            .setPositiveButton("Block") { _, _ ->
                val raw = etUrl.text.toString().trim()
                    .removePrefix("https://").removePrefix("http://").trimEnd('/')
                if (raw.isNotEmpty() && raw.contains('/')) {
                    addBlockedUrl(raw)
                } else if (raw.isNotEmpty()) {
                    val d = themedDialogBuilder()
                        .setView(themedDialogContent(
                            "Wrong URL format",
                            "Enter a URL in the format \"example.com/path\""
                        ))
                        .setPositiveButton("Got it", null).create()
                    applyDialogTheme(d); d.show()
                }
            }
            .setNegativeButton("Cancel", null).create()
        applyDialogTheme(dialog)
        dialog.window?.setSoftInputMode(android.view.WindowManager.LayoutParams.SOFT_INPUT_ADJUST_RESIZE)
        dialog.show()
    }

    private fun addBlockedUrl(url: String) {
        val current = prefs.getStringSet("blocked_urls", emptySet())?.toMutableSet() ?: mutableSetOf()
        current.add(url.lowercase())
        prefs.edit().putStringSet("blocked_urls", current).apply()
        refreshBlockedUrlsList()
    }

    private fun removeBlockedUrl(url: String) {
        val current = prefs.getStringSet("blocked_urls", emptySet())?.toMutableSet() ?: mutableSetOf()
        current.remove(url)
        prefs.edit().putStringSet("blocked_urls", current).apply()
        refreshBlockedUrlsList()
    }

    private fun refreshBlockedUrlsList() {
        blockedUrlsListContainer.removeAllViews()
        blockedUrlRowViews.clear()
        val blockedUrls = prefs.getStringSet("blocked_urls", emptySet()) ?: emptySet()
        tvUrlBlocklistEmpty.visibility = if (blockedUrls.isEmpty()) VISIBLE else GONE
        if (blockedUrls.isEmpty()) return
        blockedUrls.sortedBy { it }.forEach { url ->
            val parts = url.split("/", limit = 2)
            val domain = parts[0]
            val path = if (parts.size > 1) "/${parts[1]}" else ""

            val row = LinearLayout(this).apply {
                orientation = LinearLayout.VERTICAL
                setPadding(dp(14), dp(14), dp(14), dp(14))
                background = GradientDrawable().apply {
                    setColor(colorCard); cornerRadius = dp(10).toFloat()
                }
                layoutParams = LinearLayout.LayoutParams(
                    ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT
                ).apply { topMargin = dp(8) }
            }

            val topRow = LinearLayout(this).apply {
                orientation = LinearLayout.HORIZONTAL
                gravity = Gravity.CENTER_VERTICAL
                layoutParams = LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT)
            }
            val tvDomain = TextView(this).apply {
                text = if (path.isNotEmpty()) "$domain$path" else domain
                textSize = 16f
                setTextColor(Color.WHITE)
                maxLines = 1
                ellipsize = android.text.TextUtils.TruncateAt.END
                includeFontPadding = false
                gravity = Gravity.CENTER_VERTICAL
                setPadding(0, dp(6), 0, dp(6))
                layoutParams = LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f).apply {
                    marginEnd = dp(10)
                    topMargin = 6
                }
            }

            val btnRemove = TextView(this).apply {
                text = "✕"
                setTextColor(colorAccentRed)
                textSize = 14f
                setTypeface(null, Typeface.BOLD)
                includeFontPadding = false
                gravity = Gravity.CENTER
                background = GradientDrawable().apply {
                    shape = GradientDrawable.OVAL
                    setColor(colorAccentRedDark)
                }
                layoutParams = LinearLayout.LayoutParams(dp(28), dp(28)).apply {
                    topMargin = 6
                }
            }

            val tvStatus = TextView(this).apply {
                text = ""
                textSize = 11.9f
                setTextColor(colorAmber)
                setPadding(0, dp(8), 0, 0)
                visibility = GONE
            }

            val actionRow = LinearLayout(this).apply {
                orientation = LinearLayout.HORIZONTAL
                layoutParams = LinearLayout.LayoutParams(
                    ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT
                ).apply { topMargin = dp(8) }
            }
            val btnCancel = Button(this).apply {
                text = "Cancel"
                textSize = 10.8f
                setTextColor(colorAccentRed)
                setTypeface(null, Typeface.BOLD)
                background = GradientDrawable().apply {
                    setColor(colorAccentRedDark); cornerRadius = dp(6).toFloat()
                }
                setPadding(dp(8), dp(2), dp(8), dp(2))
                visibility = GONE
                layoutParams = LinearLayout.LayoutParams(ViewGroup.LayoutParams.WRAP_CONTENT, dp(30))
            }
            val btnConfirm = Button(this).apply {
                text = "Confirm"
                textSize = 10.8f
                setTextColor(colorGreen)
                setTypeface(null, Typeface.BOLD)
                background = GradientDrawable().apply {
                    setColor(Color.parseColor("#1B2E1E")); cornerRadius = dp(6).toFloat()
                }
                setPadding(dp(8), dp(2), dp(8), dp(2))
                visibility = GONE
                layoutParams = LinearLayout.LayoutParams(
                    ViewGroup.LayoutParams.WRAP_CONTENT, dp(30)
                ).apply { marginStart = dp(8) }
            }
            actionRow.addView(btnCancel)
            actionRow.addView(btnConfirm)

            val tvCountdown = TextView(this).apply {
                text = ""
                textSize = 14f
                setTextColor(Color.WHITE)
                setTypeface(null, Typeface.BOLD)
                includeFontPadding = false
                gravity = Gravity.CENTER_VERTICAL
                visibility = GONE
                layoutParams = LinearLayout.LayoutParams(ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT).apply {
                    topMargin = 6
                }
            }

            blockedUrlRowViews[url] = BlockedUrlRowViews(tvStatus, btnCancel, btnConfirm, btnRemove, tvCountdown)

            fun startUrlCountdownTicker(endTime: Long) {
                val handler = android.os.Handler(mainLooper)
                val ticker = object : Runnable {
                    override fun run() {
                        val currentRow = blockedUrlRowViews[url] ?: return
                        if (url !in inCountdownMode) return
                        val remaining = endTime - SystemClock.elapsedRealtime()
                        if (remaining <= 0) {
                            currentRow.tvCountdown.text = "00:00:00"
                            currentRow.tvCountdown.setOnClickListener { showUrlRemoveConfirmDialog(url) }
                        } else {
                            val h = (remaining / 3600000).toInt()
                            val m = ((remaining % 3600000) / 60000).toInt()
                            val s = ((remaining % 60000) / 1000).toInt()
                            currentRow.tvCountdown.text = String.format(Locale.US, "%02d:%02d:%02d", h, m, s)
                            currentRow.tvCountdown.setOnClickListener {
                                showResetTimerDialog {
                                    inCountdownMode.remove(url)
                                    urlCountdownEndTimes.remove(url)
                                    currentRow.tvCountdown.visibility = GONE
                                    currentRow.tvCountdown.setOnClickListener(null)
                                    blockedUrlRowViews[url]?.btnRemove?.visibility = VISIBLE
                                }
                            }
                            handler.postDelayed(this, 1000)
                        }
                    }
                }
                handler.post(ticker)
            }

            // Restore countdown UI if this URL was already counting down before the list rebuilt
            if (url in inCountdownMode) {
                btnRemove.visibility = GONE
                tvCountdown.visibility = VISIBLE
                val savedEndTime = urlCountdownEndTimes[url]
                if (savedEndTime == null || savedEndTime <= SystemClock.elapsedRealtime()) {
                    tvCountdown.text = "00:00:00"
                    tvCountdown.setOnClickListener { showUrlRemoveConfirmDialog(url) }
                } else {
                    startUrlCountdownTicker(savedEndTime)
                }
            }

            btnRemove.setOnClickListener {
                val activeDelayMinutes = prefs.getInt("saved_delay_minutes", 30)
                btnRemove.visibility = GONE
                tvCountdown.visibility = VISIBLE
                inCountdownMode.add(url)
                if (activeDelayMinutes <= 0) {
                    urlCountdownEndTimes[url] = SystemClock.elapsedRealtime() // already expired
                    tvCountdown.text = "00:00:00"
                    tvCountdown.setOnClickListener { showUrlRemoveConfirmDialog(url) }
                } else {
                    val totalMs = activeDelayMinutes * 60 * 1000L
                    val endTime = SystemClock.elapsedRealtime() + totalMs
                    urlCountdownEndTimes[url] = endTime
                    startUrlCountdownTicker(endTime)
                }
            }
            btnCancel.setOnClickListener {
                cancelPendingUrlRemove(url)
                inCountdownMode.remove(url)
                urlCountdownEndTimes.remove(url)
                tvStatus.visibility = GONE
                btnCancel.visibility = GONE
                btnConfirm.visibility = GONE
                tvCountdown.visibility = GONE
                btnRemove.visibility = VISIBLE
            }
            btnConfirm.setOnClickListener {
                prefs.edit()
                    .putBoolean("is_pending_url_remove_$url", false)
                    .putBoolean("is_awaiting_confirm_url_remove_$url", false)
                    .apply()
                endVerificationAttempted.remove("url_remove_$url")
                inCountdownMode.remove(url)
                urlCountdownEndTimes.remove(url)
                removeBlockedUrl(url)
            }

            topRow.addView(tvDomain)
            topRow.addView(btnRemove)
            topRow.addView(tvCountdown)
            row.addView(topRow)
            row.addView(tvStatus)
            row.addView(actionRow)
            blockedUrlsListContainer.addView(row)
        }
    }

    private fun showUnblockConfirmDialog(pkg: String) {
        val row = blockedAppRowViews[pkg]
        val dialog = themedDialogBuilder()
            .setView(themedDialogContent(
                "Remove block?",
                "Are you sure you want to remove this block?"
            ))
            .setPositiveButton("Confirm") { _, _ ->
                inCountdownMode.remove(pkg)
                appCountdownEndTimes.remove(pkg)
                unsuspendPackage(pkg)
            }
            .setNegativeButton("Cancel") { _, _ ->
                inCountdownMode.remove(pkg)
                appCountdownEndTimes.remove(pkg)
                row?.tvCountdown?.visibility = GONE
                row?.btnUnblock?.visibility = VISIBLE
            }
            .create()
        applyDialogTheme(dialog)
        dialog.show()
    }

    private fun showUrlRemoveConfirmDialog(url: String) {
        val row = blockedUrlRowViews[url]
        val dialog = themedDialogBuilder()
            .setView(themedDialogContent(
                "Remove block?",
                "Are you sure you want to remove this block?"
            ))
            .setPositiveButton("Confirm") { _, _ ->
                inCountdownMode.remove(url)
                urlCountdownEndTimes.remove(url)
                removeBlockedUrl(url)
            }
            .setNegativeButton("Cancel") { _, _ ->
                inCountdownMode.remove(url)
                urlCountdownEndTimes.remove(url)
                row?.tvCountdown?.visibility = GONE
                row?.btnRemove?.visibility = VISIBLE
            }
            .create()
        applyDialogTheme(dialog)
        dialog.show()
    }

    private fun confirmRemoveUrl(url: String) {
        val dialog = themedDialogBuilder()
            .setView(themedDialogContent(
                "Remove URL block?",
                "'$url' will no longer be blocked in browsers."
            ))
            .setPositiveButton("Remove") { _, _ -> removeBlockedUrl(url) }
            .setNegativeButton("Cancel", null).create()
        applyDialogTheme(dialog); dialog.show()
    }


    private fun initiateUrlRemoveDelay(url: String, minutes: Int) {
        val row = blockedUrlRowViews[url] ?: return
        val verifyKey = "url_remove_$url"
        endVerificationAttempted.remove(verifyKey)
        awaitingInitialFetch.add(verifyKey)

        val initialDurationMs = minutes * 60 * 1000L
        val initHours   = (initialDurationMs / (1000 * 60 * 60)) % 24
        val initMinutes = (initialDurationMs / (1000 * 60)) % 60
        val initSeconds = (initialDurationMs / 1000) % 60
        row.tvStatus.text = String.format(Locale.US, "%02d:%02d:%02d", initHours, initMinutes, initSeconds)
        row.tvStatus.setTextColor(colorTimerText)
        row.tvStatus.setOnClickListener(null)
        row.tvStatus.visibility  = VISIBLE
        row.btnCancel.visibility = VISIBLE
        row.btnApply.visibility  = GONE
        row.btnRemove.visibility = GONE

        retryNetworkTimeUntilSuccess(isCancelled = { verifyKey !in awaitingInitialFetch }) { networkTime ->
            val targetTime = networkTime + (minutes * 60 * 1000L)
            val currentElapsed = SystemClock.elapsedRealtime()
            prefs.edit().apply {
                putLong("target_unlock_time_url_remove_$url", targetTime)
                putLong("lock_start_elapsed_url_remove_$url", currentElapsed)
                putLong("lock_duration_ms_url_remove_$url", minutes * 60 * 1000L)
                putBoolean("is_pending_url_remove_$url", true)
                apply()
            }
            awaitingInitialFetch.remove(verifyKey)
        }
    }

    private fun cancelPendingUrlRemove(url: String) {
        val verifyKey = "url_remove_$url"
        endVerificationAttempted.remove(verifyKey)
        awaitingInitialFetch.remove(verifyKey)
        prefs.edit()
            .putBoolean("is_pending_url_remove_$url", false)
            .putBoolean("is_awaiting_confirm_url_remove_$url", false)
            .apply()
    }

    private fun updateBlockedUrlsUI() {
        val blockedUrls = prefs.getStringSet("blocked_urls", emptySet()) ?: emptySet()
        blockedUrls.toList().forEach { url ->
            val row = blockedUrlRowViews[url] ?: return@forEach
            val verifyKey = "url_remove_$url"
            val isAwaitingConfirm = prefs.getBoolean("is_awaiting_confirm_url_remove_$url", false)
            val isPending = prefs.getBoolean("is_pending_url_remove_$url", false)

            if (isAwaitingConfirm) {
                row.tvStatus.text = "00h 00m 00s"
                row.tvStatus.setTextColor(colorTimerText)
                row.tvStatus.visibility  = VISIBLE
                row.btnRemove.visibility = GONE
                row.btnCancel.visibility = VISIBLE
                row.btnApply.visibility  = VISIBLE
                return@forEach
            }
            row.btnApply.visibility = GONE

            if (!isPending) {
                if (verifyKey !in awaitingInitialFetch && url !in inCountdownMode) {
                    row.tvStatus.visibility  = GONE
                    row.btnCancel.visibility = GONE
                    row.btnRemove.visibility = VISIBLE
                }
                return@forEach
            }

            row.tvStatus.visibility  = VISIBLE
            row.btnCancel.visibility = VISIBLE
            row.btnRemove.visibility = GONE

            val targetTime     = prefs.getLong("target_unlock_time_url_remove_$url", 0L)
            val lockStartElapsed = prefs.getLong("lock_start_elapsed_url_remove_$url", 0L)
            val durationMs     = prefs.getLong("lock_duration_ms_url_remove_$url", 0L)
            val elapsedSinceLock = SystemClock.elapsedRealtime() - lockStartElapsed

            if (elapsedSinceLock < durationMs) {
                val remainingMs = durationMs - elapsedSinceLock
                val hours   = (remainingMs / (1000 * 60 * 60)) % 24
                val minutes = (remainingMs / (1000 * 60)) % 60
                val seconds = (remainingMs / 1000) % 60
                row.tvStatus.text = String.format(Locale.US, "%02d:%02d:%02d", hours, minutes, seconds)
                row.tvStatus.setTextColor(colorTimerText)
                row.tvStatus.setOnClickListener(null)
            } else {
                if (verifyKey in endVerificationAttempted) return@forEach
                if (row.tvStatus.text != "00h 00m 00s") {
                    row.tvStatus.text = "00h 00m 00s"
                    row.tvStatus.setTextColor(colorTimerText)
                }
                endVerificationAttempted.add(verifyKey)
                verifyNetworkTimeReached(targetTime, isCancelled = { verifyKey !in endVerificationAttempted }) {
                    prefs.edit()
                        .putBoolean("is_pending_url_remove_$url", false)
                        .putBoolean("is_awaiting_confirm_url_remove_$url", true)
                        .apply()
                }
            }
        }
    }

    override fun onDestroy() {
        super.onDestroy()
        timerRunnable?.let { handler.removeCallbacks(it) }
    }
}