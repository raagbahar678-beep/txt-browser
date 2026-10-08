package com.example.myapp

import android.app.Activity
import android.app.AlertDialog
import android.content.ClipData
import android.content.ClipboardManager
import android.content.ContentResolver
import android.content.Context
import android.content.Intent
import android.content.SharedPreferences
import android.content.res.Configuration
import android.database.Cursor
import android.graphics.Canvas
import android.graphics.Color
import android.graphics.Paint
import android.graphics.Path
import android.graphics.RectF
import android.graphics.Typeface
import android.graphics.drawable.GradientDrawable
import android.net.Uri
import android.os.Bundle
import android.os.Handler
import android.os.Looper
import android.os.ParcelFileDescriptor
import android.provider.DocumentsContract
import android.text.Layout
import android.text.StaticLayout
import android.text.TextPaint
import android.text.TextUtils
import android.util.TypedValue
import android.view.GestureDetector
import android.view.Gravity
import android.view.KeyEvent
import android.view.MotionEvent
import android.view.View
import android.view.ViewGroup
import android.view.WindowManager
import android.view.inputmethod.EditorInfo
import android.view.inputmethod.InputMethodManager
import android.widget.AbsListView
import android.widget.BaseAdapter
import android.widget.Button
import android.widget.EditText
import android.widget.LinearLayout
import android.widget.ListView
import android.widget.OverScroller
import android.widget.TextView
import android.widget.Toast
import java.io.BufferedInputStream
import java.io.BufferedOutputStream
import java.io.DataInputStream
import java.io.DataOutputStream
import java.io.File
import java.io.FileInputStream
import java.io.FileOutputStream
import java.io.IOException
import java.nio.ByteBuffer
import java.nio.channels.FileChannel
import java.util.Locale
import java.util.concurrent.atomic.AtomicInteger

const val MATCH = ViewGroup.LayoutParams.MATCH_PARENT
const val WRAP = ViewGroup.LayoutParams.WRAP_CONTENT
const val LINE_CAP = 16384
const val CLIP_MAX = 400000
const val SYNC_INDEX_LIMIT = 8L * 1024L * 1024L
const val NL: Byte = 10

fun fmt(n: Long): String = String.format(Locale.US, "%,d", n)

// ───────── natural sort on UTF-8 bytes (same rule as the Python natural_key) ─────────
fun lowerB(x: Int): Int = if (x in 65..90) x + 32 else x
fun isDigB(x: Int): Boolean = x in 48..57

fun naturalCompare(a: ByteArray, ao: Int, al: Int, b: ByteArray, bo: Int, bl: Int): Int {
    var i = ao
    val ae = ao + al
    var j = bo
    val be = bo + bl
    while (true) {
        while (true) {
            val ca = if (i < ae && !isDigB(a[i].toInt() and 0xFF)) (a[i].toInt() and 0xFF) else -1
            val cb = if (j < be && !isDigB(b[j].toInt() and 0xFF)) (b[j].toInt() and 0xFF) else -1
            if (ca < 0 || cb < 0) {
                if (ca >= 0) return 1
                if (cb >= 0) return -1
                break
            }
            val la = lowerB(ca)
            val lb = lowerB(cb)
            if (la != lb) return if (la < lb) -1 else 1
            i++
            j++
        }
        val aHas = i < ae
        val bHas = j < be
        if (!aHas || !bHas) {
            if (!aHas && !bHas) return 0
            return if (!aHas) -1 else 1
        }
        var si = i
        while (si < ae && a[si].toInt() == 48) si++
        var sj = j
        while (sj < be && b[sj].toInt() == 48) sj++
        var ei = si
        while (ei < ae && isDigB(a[ei].toInt() and 0xFF)) ei++
        var ej = sj
        while (ej < be && isDigB(b[ej].toInt() and 0xFF)) ej++
        val na = ei - si
        val nb = ej - sj
        if (na != nb) return if (na < nb) -1 else 1
        var k = 0
        while (k < na) {
            val d = a[si + k].toInt() - b[sj + k].toInt()
            if (d != 0) return if (d < 0) -1 else 1
            k++
        }
        i = ei
        j = ej
    }
}

fun rawCompare(a: ByteArray, ao: Int, al: Int, b: ByteArray, bo: Int, bl: Int): Int {
    val m = if (al < bl) al else bl
    var k = 0
    while (k < m) {
        val d = (a[ao + k].toInt() and 0xFF) - (b[bo + k].toInt() and 0xFF)
        if (d != 0) return d
        k++
    }
    return al - bl
}

interface IntCmp {
    fun compare(x: Int, y: Int): Int
}

fun mergeSortIdx(a: IntArray, cmp: IntCmp) {
    val n = a.size
    if (n < 2) return
    var src = a
    var dst = IntArray(n)
    var width = 1
    while (width < n) {
        var i = 0
        while (i < n) {
            val mid = if (i + width < n) i + width else n
            val hi = if (i + 2 * width < n) i + 2 * width else n
            var l = i
            var r = mid
            var k = i
            while (l < mid && r < hi) {
                if (cmp.compare(src[r], src[l]) < 0) {
                    dst[k++] = src[r++]
                } else {
                    dst[k++] = src[l++]
                }
            }
            while (l < mid) dst[k++] = src[l++]
            while (r < hi) dst[k++] = src[r++]
            i += 2 * width
        }
        val t = src
        src = dst
        dst = t
        width *= 2
    }
    if (src !== a) System.arraycopy(src, 0, a, 0, n)
}

// ───────── sparse index of a big text file (checkpoint every 128 virtual lines) ─────────
class DocIndex {
    private var offs = LongArray(1024)
    private var chs = LongArray(1024)
    private var lns = IntArray(1024)
    private var n = 0
    @Volatile var done = false
    @Volatile var totalChars = 0L
    @Volatile var totalLines = 0L

    @Synchronized fun add(o: Long, c: Long, l: Int) {
        if (n == offs.size) {
            offs = offs.copyOf(n * 2)
            chs = chs.copyOf(n * 2)
            lns = lns.copyOf(n * 2)
        }
        offs[n] = o
        chs[n] = c
        lns[n] = l
        n++
    }

    @Synchronized fun floor(o: Long): Int {
        var lo = 0
        var hi = n - 1
        var ans = 0
        while (lo <= hi) {
            val m = (lo + hi) ushr 1
            if (offs[m] <= o) { ans = m; lo = m + 1 } else hi = m - 1
        }
        return ans
    }

    @Synchronized fun floorBefore(o: Long): Int {
        var lo = 0
        var hi = n - 1
        var ans = -1
        while (lo <= hi) {
            val m = (lo + hi) ushr 1
            if (offs[m] < o) { ans = m; lo = m + 1 } else hi = m - 1
        }
        return ans
    }

    @Synchronized fun floorChars(c: Long): Int {
        var lo = 0
        var hi = n - 1
        var ans = 0
        while (lo <= hi) {
            val m = (lo + hi) ushr 1
            if (chs[m] <= c) { ans = m; lo = m + 1 } else hi = m - 1
        }
        return ans
    }

    @Synchronized fun offAt(i: Int): Long = offs[i]
    @Synchronized fun charsAt(i: Int): Long = chs[i]
    @Synchronized fun lineAt(i: Int): Int = lns[i]
    @Synchronized fun lastOffset(): Long = if (n == 0) 0L else offs[n - 1]
}

class TextSource(private val pfd: ParcelFileDescriptor, private val fis: FileInputStream, val size: Long) {
    private val ch: FileChannel = fis.channel
    @Volatile var closed = false

    fun readFully(pos: Long, dst: ByteArray, off: Int, len: Int): Int {
        if (closed) return -1
        try {
            val bb = ByteBuffer.wrap(dst, off, len)
            var total = 0
            while (bb.hasRemaining()) {
                val n = ch.read(bb, pos + total)
                if (n <= 0) break
                total += n
            }
            return total
        } catch (ex: Throwable) {
            return -1
        }
    }

    fun close() {
        closed = true
        try { fis.close() } catch (ex: Throwable) { }
        try { pfd.close() } catch (ex: Throwable) { }
    }

    companion object {
        fun open(cr: ContentResolver, uri: Uri): TextSource {
            val pfd = cr.openFileDescriptor(uri, "r") ?: throw IOException("cannot open file")
            val fis = FileInputStream(pfd.fileDescriptor)
            val size = fis.channel.size()
            return TextSource(pfd, fis, size)
        }
    }
}

class Scan {
    var end = 0
    var next = 0
    var term = false
    var chars = 0
    var breaks = 0
}

// Virtual line = text up to '\n', or at most LINE_CAP bytes (giant lines are split).
// Caller guarantees: eof reached, or at least LINE_CAP + 8 bytes available after 'from'.
fun scanLine(b: ByteArray, from: Int, limit: Int, sc: Scan) {
    var maxIdx = from + LINE_CAP
    if (maxIdx > limit - 1) maxIdx = limit - 1
    var i = from
    var found = -1
    while (i <= maxIdx) {
        if (b[i] == NL) { found = i; break }
        i++
    }
    if (found >= 0) {
        sc.end = found
        sc.next = found + 1
        sc.term = true
    } else if (limit - from <= LINE_CAP) {
        sc.end = limit
        sc.next = limit
        sc.term = false
    } else {
        var e = from + LINE_CAP
        while (e < limit && (b[e].toInt() and 0xC0) == 0x80) e++
        sc.end = e
        sc.next = e
        sc.term = false
    }
    var c = 0
    var cr = 0
    var k = from
    val e2 = sc.end
    while (k < e2) {
        val x = b[k].toInt()
        if ((x and 0xC0) != 0x80) c++
        if (x == 13) cr++
        k++
    }
    if (sc.term) {
        if (e2 > from && b[e2 - 1].toInt() == 13) { c--; cr-- }
        c++
        sc.breaks = cr + 1
    } else {
        sc.breaks = cr
    }
    sc.chars = c
}

class LineItem(
    val start: Long, val next: Long, val text: String, val term: Boolean,
    val charsBefore: Long, val lineNo: Int, val colBase: Int,
    val lineChars: Int, val lineBreaks: Int
) {
    var layout: StaticLayout? = null
    var layoutWidth: Int = -1
    var height: Int = 0
    var hlPath: Path? = null
    var hlFor: String? = null
    fun nextColBase(): Int = if (term) 0 else colBase + lineChars
}

class LineReader(private val src: TextSource) {
    private val buf = ByteArray(256 * 1024)
    private var bufStart = -1L
    private var bufLen = 0
    private val sc = Scan()

    fun read(start: Long, chars: Long, line: Int, colBase: Int): LineItem? {
        val size = src.size
        if (start < 0L || start >= size) return null
        if (bufStart < 0L || start < bufStart || (start + LINE_CAP + 8 > bufStart + bufLen && bufStart + bufLen < size)) {
            val n = src.readFully(start, buf, 0, buf.size)
            if (n <= 0) { bufStart = -1L; bufLen = 0; return null }
            bufStart = start
            bufLen = n
        }
        val from = (start - bufStart).toInt()
        if (from >= bufLen) return null
        scanLine(buf, from, bufLen, sc)
        var text = String(buf, from, sc.end - from, Charsets.UTF_8)
        if (sc.term && text.endsWith("\r")) text = text.substring(0, text.length - 1)
        if (text.indexOf('\r') >= 0) text = text.replace('\r', '\n')
        return LineItem(start, bufStart + sc.next, text, sc.term, chars, line, colBase, sc.chars, sc.breaks)
    }
}

fun buildDocIndex(src: TextSource, di: DocIndex, cancelled: () -> Boolean, progress: (Long) -> Unit): Boolean {
    val size = src.size
    di.add(0L, 0L, 0)
    if (size <= 0L) {
        di.totalChars = 0L
        di.totalLines = 0L
        di.done = true
        return true
    }
    val buf = ByteArray(1 shl 20)
    var filePos = 0L
    var have = 0
    var pos = 0
    var eof = false
    var vline = 0L
    var chars = 0L
    var lines = 0L
    val sc = Scan()
    while (true) {
        if (!eof && have - pos < LINE_CAP + 8) {
            if (cancelled()) return false
            val rem = have - pos
            if (rem > 0) System.arraycopy(buf, pos, buf, 0, rem)
            filePos += pos
            have = rem
            pos = 0
            val want = buf.size - have
            val n = src.readFully(filePos + have, buf, have, want)
            if (n < 0) return false
            have += n
            if (n < want) eof = true
            progress(filePos)
        }
        if (pos >= have) break
        scanLine(buf, pos, have, sc)
        chars += sc.chars
        lines += sc.breaks
        vline++
        pos = sc.next
        if ((vline and 127L) == 0L && filePos + pos < size) di.add(filePos + pos, chars, lines.toInt())
    }
    di.totalChars = chars
    di.totalLines = lines + 1L
    di.done = true
    return true
}

// ───────── compact, sorted list of .txt files (works for millions of names) ─────────
class FileIndex(
    val buf: ByteArray, val offs: IntArray, val order: IntArray,
    val prefix: String, val exc: HashMap<Int, String>?
) {
    val size: Int get() = order.size

    fun name(i: Int): String {
        val k = order[i]
        return String(buf, offs[k], offs[k + 1] - offs[k], Charsets.UTF_8)
    }

    fun docId(i: Int): String {
        val k = order[i]
        val e = exc?.get(k)
        if (e != null) return e
        return prefix + name(i)
    }

    fun indexOf(name: String): Int {
        val nb = name.toByteArray(Charsets.UTF_8)
        for (i in 0 until order.size) {
            val k = order[i]
            val s = offs[k]
            if (offs[k + 1] - s != nb.size) continue
            var same = true
            var q = 0
            while (q < nb.size) {
                if (buf[s + q] != nb[q]) { same = false; break }
                q++
            }
            if (same) return i
        }
        return -1
    }

    fun signature(): Long {
        var h = -3750763034362895579L
        for (i in 0 until order.size) {
            val k = order[i]
            var p = offs[k]
            val e = offs[k + 1]
            while (p < e) {
                h = (h xor (buf[p].toLong() and 0xFFL)) * 1099511628211L
                p++
            }
            h = h * 31L + 7L
        }
        return h xor order.size.toLong()
    }
}

fun scanFolder(cr: ContentResolver, tree: Uri, report: (Int) -> Unit, cancelled: () -> Boolean): FileIndex? {
    val treeDocId = DocumentsContract.getTreeDocumentId(tree)
    val childrenUri = DocumentsContract.buildChildDocumentsUriUsingTree(tree, treeDocId)
    val prefix = if (treeDocId.endsWith(":")) treeDocId else "$treeDocId/"
    var buf = ByteArray(1 shl 20)
    var blen = 0
    var offs = IntArray(4096)
    var cnt = 0
    var exc: HashMap<Int, String>? = null
    val proj = arrayOf(
        DocumentsContract.Document.COLUMN_DOCUMENT_ID,
        DocumentsContract.Document.COLUMN_DISPLAY_NAME,
        DocumentsContract.Document.COLUMN_MIME_TYPE
    )
    val cur: Cursor = cr.query(childrenUri, proj, null, null, null) ?: throw IOException("Cannot list folder")
    try {
        var rows = 0
        while (cur.moveToNext()) {
            rows++
            if ((rows and 1023) == 0 && cancelled()) return null
            val name = cur.getString(1) ?: continue
            if (!name.endsWith(".txt", ignoreCase = true)) continue
            if (DocumentsContract.Document.MIME_TYPE_DIR == cur.getString(2)) continue
            val id = cur.getString(0) ?: continue
            val nb = name.toByteArray(Charsets.UTF_8)
            if (blen + nb.size > buf.size) buf = buf.copyOf(maxOf(buf.size * 2, blen + nb.size))
            System.arraycopy(nb, 0, buf, blen, nb.size)
            if (cnt + 2 > offs.size) offs = offs.copyOf(offs.size * 2)
            offs[cnt] = blen
            blen += nb.size
            val normal = id.length == prefix.length + name.length && id.startsWith(prefix) && id.endsWith(name)
            if (!normal) {
                var m = exc
                if (m == null) {
                    m = HashMap()
                    exc = m
                }
                m[cnt] = id
            }
            cnt++
            if (cnt % 2000 == 0) report(cnt)
        }
    } finally {
        cur.close()
    }
    offs[cnt] = blen
    val b2 = buf.copyOf(blen)
    val o2 = offs.copyOf(cnt + 1)
    val order = IntArray(cnt)
    for (i in 0 until cnt) order[i] = i
    mergeSortIdx(order, object : IntCmp {
        override fun compare(x: Int, y: Int): Int {
            val ax = o2[x]
            val al = o2[x + 1] - ax
            val ay = o2[y]
            val bl = o2[y + 1] - ay
            val c = naturalCompare(b2, ax, al, b2, ay, bl)
            if (c != 0) return c
            return rawCompare(b2, ax, al, b2, ay, bl)
        }
    })
    return FileIndex(b2, o2, order, prefix, exc)
}

object IndexCache {
    private fun writeInts(o: DataOutputStream, a: IntArray) {
        val bb = ByteBuffer.allocate(a.size * 4)
        bb.asIntBuffer().put(a)
        o.write(bb.array())
    }

    private fun readInts(i: DataInputStream, n: Int): IntArray {
        val bytes = ByteArray(n * 4)
        i.readFully(bytes)
        val r = IntArray(n)
        ByteBuffer.wrap(bytes).asIntBuffer().get(r)
        return r
    }

    fun save(ctx: Context, tree: String, fi: FileIndex) {
        try {
            val tmp = File(ctx.filesDir, "folder_index.tmp")
            val o = DataOutputStream(BufferedOutputStream(FileOutputStream(tmp), 1 shl 16))
            try {
                o.writeInt(0x54425831)
                o.writeUTF(tree)
                o.writeUTF(fi.prefix)
                o.writeInt(fi.size)
                o.writeInt(fi.buf.size)
                o.write(fi.buf)
                writeInts(o, fi.offs)
                writeInts(o, fi.order)
                val e = fi.exc
                o.writeInt(if (e == null) 0 else e.size)
                if (e != null) {
                    for ((k, v) in e) {
                        o.writeInt(k)
                        o.writeUTF(v)
                    }
                }
            } finally {
                o.close()
            }
            tmp.renameTo(File(ctx.filesDir, "folder_index.bin"))
        } catch (ex: Throwable) { }
    }

    fun load(ctx: Context, tree: String): FileIndex? {
        try {
            val f = File(ctx.filesDir, "folder_index.bin")
            if (!f.exists()) return null
            val i = DataInputStream(BufferedInputStream(FileInputStream(f), 1 shl 16))
            try {
                if (i.readInt() != 0x54425831) return null
                if (i.readUTF() != tree) return null
                val prefix = i.readUTF()
                val n = i.readInt()
                val bl = i.readInt()
                val buf = ByteArray(bl)
                i.readFully(buf)
                val offs = readInts(i, n + 1)
                val order = readInts(i, n)
                val ec = i.readInt()
                var exc: HashMap<Int, String>? = null
                if (ec > 0) {
                    val m = HashMap<Int, String>()
                    for (q in 0 until ec) {
                        val k = i.readInt()
                        m[k] = i.readUTF()
                    }
                    exc = m
                }
                return FileIndex(buf, offs, order, prefix, exc)
            } finally {
                i.close()
            }
        } catch (ex: Throwable) {
            return null
        }
    }
}

class Hit(val item: LineItem, val ch: Int, val cp: Int) {
    val abs: Long get() = item.charsBefore + cp
}

// Virtual text viewer: only the lines near the screen are ever loaded, so GB files are smooth.
class TextCanvas(ctx: Context) : View(ctx) {
    private val density = ctx.resources.displayMetrics.density
    private val padX = (12 * density).toInt()
    private val padV = (3 * density).toInt()
    private val paint = TextPaint(Paint.ANTI_ALIAS_FLAG)
    private val hlPaint = Paint()
    private val selPaint = Paint()
    private val tipBg = Paint(Paint.ANTI_ALIAS_FLAG)
    private val tipFg = TextPaint(Paint.ANTI_ALIAS_FLAG)
    private val tmpPath = Path()
    private val tipRect = RectF()
    private val items = ArrayList<LineItem>()
    private var src: TextSource? = null
    private var reader: LineReader? = null
    var docIndex: DocIndex? = null
    private var topItem = 0
    private var topOff = 0f
    private var atEof = true
    private var viewH = 0
    private var contentW = 0
    private var hlTerm: String? = null
    private var selAnchor = -1L
    private var selCaret = -1L
    private var selecting = false
    private var mouseSel = false
    private var pendingOffset = -1L
    private var pendingFraction = -1.0
    private var pendingFocus = false
    var caretLn = 1
    var caretCol = 1
    private var tipStr: String? = null
    private var tipX = 0f
    private var tipY = 0f
    private val uiHandler = Handler(Looper.getMainLooper())
    private val hideTipRun = Runnable { tipStr = null; invalidate() }
    private val scroller = OverScroller(ctx)
    private var lastFlingY = 0
    var onScrolled: (() -> Unit)? = null
    var onSelection: (() -> Unit)? = null
    var onCaret: (() -> Unit)? = null
    var onContextMenu: (() -> Unit)? = null
    var onTouched: (() -> Unit)? = null
    private val gd: GestureDetector

    init {
        isFocusable = true
        isFocusableInTouchMode = true
        val dm = ctx.resources.displayMetrics
        paint.typeface = Typeface.SERIF
        paint.textSize = TypedValue.applyDimension(TypedValue.COMPLEX_UNIT_SP, 15f, dm)
        paint.color = Color.parseColor("#111111")
        hlPaint.color = Color.parseColor("#FFF176")
        selPaint.color = Color.parseColor("#C8E0FF")
        tipBg.color = Color.parseColor("#1E1E1E")
        tipFg.color = Color.WHITE
        tipFg.typeface = Typeface.DEFAULT_BOLD
        tipFg.textSize = TypedValue.applyDimension(TypedValue.COMPLEX_UNIT_SP, 11f, dm)
        gd = GestureDetector(ctx, object : GestureDetector.SimpleOnGestureListener() {
            override fun onDown(e: MotionEvent): Boolean {
                scroller.forceFinished(true)
                return true
            }

            override fun onScroll(e1: MotionEvent?, e2: MotionEvent, dx: Float, dy: Float): Boolean {
                if (!selecting) scrollBy(dy)
                return true
            }

            override fun onFling(e1: MotionEvent?, e2: MotionEvent, vx: Float, vy: Float): Boolean {
                if (selecting) return true
                lastFlingY = 0
                scroller.fling(0, 0, 0, (-vy).toInt(), 0, 0, -1000000000, 1000000000)
                postInvalidateOnAnimation()
                return true
            }

            override fun onSingleTapUp(e: MotionEvent): Boolean {
                handleTap(e.x, e.y)
                return true
            }

            override fun onLongPress(e: MotionEvent) {
                startTouchSelection(e.x, e.y)
            }
        })
    }

    // ── basic helpers ──
    private fun cw(): Int = if (contentW > 60) contentW else 400

    private fun buildLayout(li: LineItem) {
        val w = cw()
        val sl = StaticLayout.Builder.obtain(li.text, 0, li.text.length, paint, w)
            .setBreakStrategy(Layout.BREAK_STRATEGY_SIMPLE)
            .setHyphenationFrequency(Layout.HYPHENATION_FREQUENCY_NONE)
            .setIncludePad(false)
            .build()
        li.layout = sl
        li.layoutWidth = w
        li.height = sl.height + 2 * padV
        li.hlPath = null
    }

    private fun hOf(li: LineItem): Int {
        if (li.layout == null || li.layoutWidth != cw()) buildLayout(li)
        return li.height
    }

    private fun layoutOf(li: LineItem): StaticLayout {
        hOf(li)
        return li.layout!!
    }

    fun lineStep(): Float = paint.fontSpacing

    fun currentSource(): TextSource? = src

    private fun closeSource() {
        val s = src
        if (s != null) s.close()
        src = null
        reader = null
        docIndex = null
    }

    fun release() {
        closeSource()
        items.clear()
    }

    // ── content loading ──
    fun showMessage(msg: String) {
        closeSource()
        items.clear()
        items.add(LineItem(0L, 0L, msg, false, 0L, 0, 0, msg.length, 0))
        topItem = 0
        topOff = 0f
        atEof = true
        selAnchor = -1L
        selCaret = -1L
        hlTerm = null
        pendingOffset = -1L
        pendingFraction = -1.0
        caretLn = 1
        caretCol = 1
        scroller.forceFinished(true)
        invalidate()
        onScrolled?.invoke()
    }

    fun attach(s: TextSource, di: DocIndex) {
        closeSource()
        src = s
        docIndex = di
        reader = LineReader(s)
        selAnchor = -1L
        selCaret = -1L
        pendingOffset = -1L
        pendingFraction = -1.0
        caretLn = 1
        caretCol = 1
        scroller.forceFinished(true)
        loadFirst()
        invalidate()
        onScrolled?.invoke()
    }

    private fun loadFirst() {
        items.clear()
        topItem = 0
        topOff = 0f
        val s = src
        val rd = reader
        if (s == null || rd == null) { atEof = true; return }
        val li = rd.read(0L, 0L, 0, 0)
        if (li != null) {
            items.add(li)
            atEof = li.next >= s.size
        } else {
            atEof = true
        }
    }

    fun setHighlight(term: String?) {
        hlTerm = if (term != null && term.isNotEmpty()) term else null
        for (li in items) { li.hlPath = null; li.hlFor = null }
        invalidate()
    }

    fun setPending(off: Long, frac: Double, focus: Boolean) {
        pendingOffset = off
        pendingFraction = frac
        pendingFocus = focus
    }

    fun applyPending() {
        val o = pendingOffset
        val f = pendingFraction
        val foc = pendingFocus
        pendingOffset = -1L
        pendingFraction = -1.0
        pendingFocus = false
        if (o >= 0L) jumpToOffset(o, foc) else if (f >= 0.0) jumpToFraction(f)
    }

    fun goTop() {
        if (src != null) loadFirst()
        invalidate()
        onScrolled?.invoke()
    }

    fun goBottom() {
        val s = src ?: return
        if (jumpToOffset(s.size - 1L, false)) {
            scrollBy(-viewH.toFloat())
            scrollBy(1e9f)
        }
    }

    fun jumpToFraction(f: Double): Boolean {
        val s = src ?: return false
        if (f <= 0.0) { goTop(); return true }
        val di = docIndex ?: return false
        val off = (if (f > 1.0) 1.0 else f) * s.size.toDouble()
        if (!di.done) {
            pendingOffset = -1L
            pendingFraction = f
            return false
        }
        return jumpToOffset(off.toLong(), false)
    }

    fun jumpToOffset(offset0: Long, focusTerm: Boolean): Boolean {
        val s = src ?: return false
        val di = docIndex ?: return false
        val rd = reader ?: return false
        if (!di.done) {
            pendingOffset = offset0
            pendingFocus = focusTerm
            return false
        }
        val maxOff = if (s.size > 0L) s.size - 1L else 0L
        val offset = if (offset0 < 0L) 0L else if (offset0 > maxOff) maxOff else offset0
        val cp = di.floor(offset)
        var pos = di.offAt(cp)
        var chars = di.charsAt(cp)
        var line = di.lineAt(cp)
        var col = 0
        var found: LineItem? = null
        while (true) {
            val li = rd.read(pos, chars, line, col) ?: break
            if (li.next > offset) { found = li; break }
            pos = li.next
            chars += li.lineChars
            line += li.lineBreaks
            col = li.nextColBase()
        }
        val f = found ?: return false
        items.clear()
        items.add(f)
        topItem = 0
        topOff = 0f
        atEof = f.next >= s.size
        if (focusTerm) {
            val term = hlTerm
            if (term != null) {
                val p = f.text.indexOf(term, 0, true)
                if (p >= 0) {
                    val lay = layoutOf(f)
                    val ln = lay.getLineForOffset(p)
                    topOff = (lay.getLineTop(ln) + padV).toFloat()
                }
            }
            scrollBy(-viewH * 0.3f)
        }
        invalidate()
        onScrolled?.invoke()
        return true
    }

    // ── window management ──
    private fun appendLine(): LineItem? {
        val rd = reader
        val s = src
        if (rd == null || s == null || items.isEmpty()) { atEof = true; return null }
        val last = items[items.size - 1]
        if (last.next >= s.size) { atEof = true; return null }
        val li = rd.read(last.next, last.charsBefore + last.lineChars, last.lineNo + last.lineBreaks, last.nextColBase())
        if (li == null) { atEof = true; return null }
        items.add(li)
        if (li.next >= s.size) atEof = true
        return li
    }

    private fun prependLines(): Boolean {
        val rd = reader ?: return false
        val di = docIndex ?: return false
        if (items.isEmpty()) return false
        val first = items[0]
        if (first.start <= 0L) return false
        val cpI = di.floorBefore(first.start)
        if (cpI < 0) return false
        var pos = di.offAt(cpI)
        var chars = di.charsAt(cpI)
        var line = di.lineAt(cpI)
        var col = 0
        val tmp = ArrayList<LineItem>()
        while (pos < first.start && tmp.size < 2000) {
            val li = rd.read(pos, chars, line, col) ?: break
            tmp.add(li)
            pos = li.next
            chars += li.lineChars
            line += li.lineBreaks
            col = li.nextColBase()
        }
        while (tmp.isNotEmpty() && tmp[tmp.size - 1].next > first.start) tmp.removeAt(tmp.size - 1)
        if (tmp.isEmpty()) return false
        items.addAll(0, tmp)
        topItem += tmp.size
        return true
    }

    private fun ensureForward(px: Float) {
        var sum = -topOff
        var i = topItem
        while (i < items.size) { sum += hOf(items[i]); i++ }
        var guard = 0
        while (sum < px && !atEof && guard < 2000) {
            val li = appendLine() ?: break
            sum += hOf(li)
            guard++
        }
    }

    private fun remainingBelow(): Float {
        if (!atEof) return Float.MAX_VALUE
        var sum = 0f
        var i = topItem
        while (i < items.size) { sum += hOf(items[i]); i++ }
        return sum - topOff - viewH
    }

    private fun normalizeDown() {
        while (topItem < items.size - 1) {
            val h = hOf(items[topItem])
            if (topOff >= h) { topOff -= h; topItem++ } else break
        }
    }

    private fun trimTop() {
        if (topItem <= 80) return
        val di = docIndex ?: return
        val n = topItem - 40
        if (!(di.done || di.lastOffset() > items[n].start)) return
        items.subList(0, n).clear()
        topItem -= n
    }

    fun scrollBy(dy: Float): Float {
        if (items.isEmpty() || viewH <= 0) return 0f
        var moved = 0f
        if (dy > 0f) {
            ensureForward(dy + viewH)
            val rem = remainingBelow()
            var d = dy
            if (d > rem) d = if (rem > 0f) rem else 0f
            topOff += d
            normalizeDown()
            moved = d
            trimTop()
        } else if (dy < 0f) {
            var need = -dy
            while (need > 0f) {
                if (topOff >= need) {
                    topOff -= need
                    moved -= need
                    need = 0f
                } else {
                    moved -= topOff
                    need -= topOff
                    topOff = 0f
                    if (topItem == 0) {
                        if (!prependLines()) break
                        if (topItem == 0) break
                    }
                    topItem--
                    topOff = hOf(items[topItem]).toFloat()
                }
            }
        }
        if (moved != 0f) {
            invalidate()
            onScrolled?.invoke()
        }
        return moved
    }

    fun scrollLines(n: Int) {
        scrollBy(n * lineStep() * 1.5f)
    }

    fun pageScroll(dir: Int) {
        scrollBy(dir * viewH * 0.9f)
    }

    fun scrollFraction(): Double {
        val s = src ?: return 0.0
        if (s.size <= 0L || items.isEmpty() || topItem >= items.size) return 0.0
        val li = items[topItem]
        val h = hOf(li)
        val within = if (h > 0) (topOff / h).coerceIn(0f, 1f).toDouble() else 0.0
        return (li.start + (li.next - li.start) * within) / s.size.toDouble()
    }

    fun visibleFraction(): Double {
        val s = src ?: return 1.0
        if (s.size <= 0L || items.isEmpty() || viewH <= 0) return 1.0
        var y = -topOff
        var i = topItem
        var bytes = 0.0
        while (i < items.size && y < viewH) {
            val li = items[i]
            val h = hOf(li)
            if (h > 0) {
                val top = maxOf(y, 0f)
                val bot = minOf(y + h, viewH.toFloat())
                if (bot > top) bytes += (li.next - li.start).toDouble() * ((bot - top) / h).toDouble()
            }
            y += h
            i++
        }
        val f = bytes / s.size.toDouble()
        return if (f > 1.0) 1.0 else if (f < 0.0) 0.0 else f
    }

    // ── drawing ──
    override fun onSizeChanged(w: Int, h: Int, oldw: Int, oldh: Int) {
        super.onSizeChanged(w, h, oldw, oldh)
        viewH = h
        contentW = w - 2 * padX
        if (items.isNotEmpty()) normalizeDown()
        invalidate()
        onScrolled?.invoke()
    }

    override fun onDraw(canvas: Canvas) {
        canvas.drawColor(Color.WHITE)
        if (items.isEmpty() || viewH <= 0) return
        ensureForward(viewH.toFloat() * 1.5f)
        var y = -topOff
        var i = topItem
        while (i < items.size && y < viewH) {
            val li = items[i]
            val h = hOf(li)
            if (y + h > 0f) drawItem(canvas, li, y)
            y += h
            i++
        }
        drawTip(canvas)
    }

    private fun buildHl(li: LineItem, lay: StaticLayout, term: String) {
        val p = Path()
        var from = 0
        var count = 0
        while (count < 300) {
            val i = li.text.indexOf(term, from, true)
            if (i < 0) break
            lay.getSelectionPath(i, i + term.length, tmpPath)
            p.addPath(tmpPath)
            from = i + term.length
            count++
        }
        li.hlPath = p
        li.hlFor = term
    }

    private fun drawItem(c: Canvas, li: LineItem, y: Float) {
        val lay = li.layout ?: return
        c.save()
        c.translate(padX.toFloat(), y + padV)
        val term = hlTerm
        if (term != null) {
            if (li.hlPath == null || li.hlFor != term) buildHl(li, lay, term)
            val hp = li.hlPath
            if (hp != null) c.drawPath(hp, hlPaint)
        }
        if (selAnchor >= 0L && selCaret >= 0L && selAnchor != selCaret) {
            val a = minOf(selAnchor, selCaret)
            val b = maxOf(selAnchor, selCaret)
            val cpCount = li.text.codePointCount(0, li.text.length)
            val lineAbs = li.charsBefore
            if (b > lineAbs && a < lineAbs + li.lineChars) {
                val lo = maxOf(a - lineAbs, 0L)
                val hi = minOf(b - lineAbs, cpCount.toLong())
                if (hi > lo) {
                    val loCh = li.text.offsetByCodePoints(0, lo.toInt())
                    val hiCh = li.text.offsetByCodePoints(0, hi.toInt())
                    if (loCh <= 0 && hiCh >= li.text.length) {
                        c.drawRect(0f, 0f, lay.width.toFloat(), lay.height.toFloat(), selPaint)
                    } else {
                        lay.getSelectionPath(loCh, hiCh, tmpPath)
                        c.drawPath(tmpPath, selPaint)
                    }
                }
            }
        }
        lay.draw(c)
        c.restore()
    }

    private fun drawTip(c: Canvas) {
        val t = tipStr ?: return
        val px = 6 * density
        val py = 4 * density
        val w = tipFg.measureText(t) + 2 * px
        val h = tipFg.fontSpacing + 2 * py
        var x = tipX
        var y = tipY
        if (x + w > width) x = width - w
        if (y + h > height) y = height - h
        if (x < 0f) x = 0f
        if (y < 0f) y = 0f
        tipRect.set(x, y, x + w, y + h)
        c.drawRoundRect(tipRect, 4 * density, 4 * density, tipBg)
        c.drawText(t, x + px, y + py - tipFg.fontMetrics.ascent, tipFg)
    }

    override fun computeScroll() {
        if (scroller.computeScrollOffset()) {
            val y = scroller.currY
            val dy = y - lastFlingY
            lastFlingY = y
            val moved = scrollBy(dy.toFloat())
            if (moved == 0f && dy != 0) scroller.forceFinished(true) else postInvalidateOnAnimation()
        }
    }

    // ── hit testing, caret, tooltip ──
    private fun hit(x: Float, y: Float): Hit? {
        if (items.isEmpty()) return null
        var yy = -topOff
        var i = topItem
        var best: LineItem? = null
        var bestTop = 0f
        while (i < items.size) {
            val li = items[i]
            val h = hOf(li)
            best = li
            bestTop = yy
            if (y < yy + h) break
            yy += h
            i++
        }
        val li2 = best ?: return null
        val lay = li2.layout ?: return null
        var ly = (y - bestTop - padV).toInt()
        if (ly < 0) ly = 0
        if (ly > lay.height - 1) ly = lay.height - 1
        val line = lay.getLineForVertical(ly)
        var off = lay.getOffsetForHorizontal(line, x - padX)
        if (off < 0) off = 0
        if (off > li2.text.length) off = li2.text.length
        return Hit(li2, off, li2.text.codePointCount(0, off))
    }

    private fun setCaret(h: Hit) {
        caretLn = h.item.lineNo + 1
        caretCol = h.item.colBase + h.cp + 1
        onCaret?.invoke()
    }

    private fun showTip(x: Float, y: Float, h: Hit, yOff: Float) {
        tipStr = "Char " + fmt(h.item.charsBefore + h.cp) + "  (Ln " + (h.item.lineNo + 1) + ", Col " + (h.item.colBase + h.cp + 1) + ")"
        tipX = x + 18 * density
        tipY = y + yOff
        uiHandler.removeCallbacks(hideTipRun)
        uiHandler.postDelayed(hideTipRun, 3000)
        invalidate()
    }

    private fun hideTip() {
        tipStr = null
        uiHandler.removeCallbacks(hideTipRun)
        invalidate()
    }

    private fun handleTap(x: Float, y: Float) {
        if (selAnchor >= 0L) {
            selAnchor = -1L
            selCaret = -1L
            onSelection?.invoke()
        }
        val h = hit(x, y)
        if (h != null) {
            setCaret(h)
            showTip(x, y, h, -56 * density)
        }
        invalidate()
    }

    // ── selection ──
    fun selectionRange(): LongArray? {
        if (selAnchor < 0L || selCaret < 0L || selAnchor == selCaret) return null
        return if (selAnchor < selCaret) longArrayOf(selAnchor, selCaret) else longArrayOf(selCaret, selAnchor)
    }

    fun selectAll(total: Long) {
        selAnchor = 0L
        selCaret = total
        caretLn = 1
        caretCol = 1
        goTop()
        invalidate()
        onSelection?.invoke()
    }

    private fun startTouchSelection(x: Float, y: Float) {
        val h = hit(x, y) ?: return
        val t = h.item.text
        var s = h.ch
        var e = h.ch
        while (s > 0 && Character.isLetterOrDigit(t[s - 1])) s--
        while (e < t.length && Character.isLetterOrDigit(t[e])) e++
        if (s == e && e < t.length) e++
        val base = h.item.charsBefore
        selAnchor = base + t.codePointCount(0, s)
        selCaret = base + t.codePointCount(0, e)
        selecting = true
        invalidate()
        onSelection?.invoke()
    }

    private fun extendSelection(x: Float, y: Float) {
        val h = hit(x, y) ?: return
        selCaret = h.abs
        if (y < 40 * density) scrollBy(-14 * density) else if (y > height - 40 * density) scrollBy(14 * density)
        invalidate()
        onSelection?.invoke()
    }

    // ── input ──
    private fun handleMouse(ev: MotionEvent): Boolean {
        when (ev.actionMasked) {
            MotionEvent.ACTION_DOWN -> {
                if ((ev.buttonState and MotionEvent.BUTTON_SECONDARY) != 0) {
                    onContextMenu?.invoke()
                    return true
                }
                val h = hit(ev.x, ev.y)
                if (h != null) {
                    selAnchor = h.abs
                    selCaret = h.abs
                    setCaret(h)
                    mouseSel = true
                    hideTip()
                    onSelection?.invoke()
                }
            }
            MotionEvent.ACTION_MOVE -> {
                if (mouseSel) extendSelection(ev.x, ev.y)
            }
            MotionEvent.ACTION_UP, MotionEvent.ACTION_CANCEL -> {
                if (mouseSel) {
                    mouseSel = false
                    if (selAnchor == selCaret) {
                        selAnchor = -1L
                        selCaret = -1L
                    }
                    invalidate()
                    onSelection?.invoke()
                }
            }
            else -> { }
        }
        return true
    }

    override fun onTouchEvent(ev: MotionEvent): Boolean {
        if (ev.actionMasked == MotionEvent.ACTION_DOWN) {
            requestFocus()
            onTouched?.invoke()
        }
        if (ev.getToolType(0) == MotionEvent.TOOL_TYPE_MOUSE) return handleMouse(ev)
        if (selecting) {
            when (ev.actionMasked) {
                MotionEvent.ACTION_MOVE -> extendSelection(ev.x, ev.y)
                MotionEvent.ACTION_UP -> {
                    selecting = false
                    invalidate()
                    if (selectionRange() != null) onContextMenu?.invoke()
                }
                MotionEvent.ACTION_CANCEL -> selecting = false
                else -> { }
            }
        }
        gd.onTouchEvent(ev)
        return true
    }

    override fun onGenericMotionEvent(ev: MotionEvent): Boolean {
        when (ev.actionMasked) {
            MotionEvent.ACTION_SCROLL -> {
                val v = ev.getAxisValue(MotionEvent.AXIS_VSCROLL)
                scrollBy(-v * lineStep() * 3f)
                return true
            }
            MotionEvent.ACTION_HOVER_MOVE -> {
                val h = hit(ev.x, ev.y)
                if (h != null) showTip(ev.x, ev.y, h, 22 * density)
                return true
            }
            MotionEvent.ACTION_HOVER_EXIT -> {
                hideTip()
                return true
            }
            else -> { }
        }
        return super.onGenericMotionEvent(ev)
    }
}

// Reads the selected range (absolute character positions) straight from the file, capped for the clipboard.
fun extractRange(s: TextSource, di: DocIndex?, a: Long, b: Long, maxChars: Int): Pair<String, Boolean> {
    val rd = LineReader(s)
    var pos = 0L
    var chars = 0L
    var line = 0
    var col = 0
    if (di != null) {
        val cp = di.floorChars(a)
        pos = di.offAt(cp)
        chars = di.charsAt(cp)
        line = di.lineAt(cp)
    }
    val sb = StringBuilder()
    var truncated = false
    while (chars < b) {
        val li = rd.read(pos, chars, line, col) ?: break
        val cpCount = li.text.codePointCount(0, li.text.length)
        val lineEndAbs = chars + li.lineChars
        if (lineEndAbs > a) {
            val relA = maxOf(a - chars, 0L)
            val relB = minOf(b - chars, cpCount.toLong())
            if (relB > relA) {
                val sIdx = li.text.offsetByCodePoints(0, relA.toInt())
                val eIdx = li.text.offsetByCodePoints(0, relB.toInt())
                sb.append(li.text, sIdx, eIdx)
            }
            if (li.term && b > chars + cpCount && a <= chars + cpCount) sb.append('\n')
            if (sb.length >= maxChars) { truncated = true; break }
        }
        pos = li.next
        chars += li.lineChars
        line += li.lineBreaks
        col = li.nextColBase()
    }
    var out = sb.toString()
    if (out.length > maxChars) {
        out = out.substring(0, maxChars)
        truncated = true
    }
    return Pair(out, truncated)
}

class VScrollBar(ctx: Context) : View(ctx) {
    private val density = ctx.resources.displayMetrics.density
    private val trackP = Paint()
    private val thumbP = Paint(Paint.ANTI_ALIAS_FLAG)
    private val rect = RectF()
    private var pos = 0.0
    private var size = 1.0
    var onDrag: ((Double) -> Unit)? = null

    init {
        trackP.color = Color.parseColor("#F0F0F0")
        thumbP.color = Color.parseColor("#BBBBBB")
    }

    fun set(p: Double, s: Double) {
        pos = p
        size = s
        invalidate()
    }

    private fun thumbLen(): Float {
        val l = (size * height).toFloat()
        val m = if (l > 36 * density) l else 36 * density
        return if (m > height) height.toFloat() else m
    }

    private fun thumbTop(th: Float): Float {
        val room = height - th
        val maxPos = 1.0 - size
        val f = if (maxPos > 1e-9) (pos / maxPos).coerceIn(0.0, 1.0) else 0.0
        return (room * f).toFloat()
    }

    override fun onDraw(c: Canvas) {
        c.drawRect(0f, 0f, width.toFloat(), height.toFloat(), trackP)
        val th = thumbLen()
        val top = thumbTop(th)
        rect.set(3 * density, top, width - 3 * density, top + th)
        c.drawRoundRect(rect, 4 * density, 4 * density, thumbP)
    }

    override fun onTouchEvent(ev: MotionEvent): Boolean {
        when (ev.actionMasked) {
            MotionEvent.ACTION_DOWN, MotionEvent.ACTION_MOVE -> {
                parent.requestDisallowInterceptTouchEvent(true)
                val th = thumbLen()
                val room = height - th
                if (room > 0f) {
                    val frac = ((ev.y - th / 2f) / room).toDouble().coerceIn(0.0, 1.0)
                    var maxPos = 1.0 - size
                    if (maxPos < 0.0) maxPos = 0.0
                    onDrag?.invoke(frac * maxPos)
                }
            }
            else -> { }
        }
        return true
    }
}

class MainActivity : Activity() {
    private val uiHandler = Handler(Looper.getMainLooper())
    private lateinit var prefs: SharedPreferences
    private var folderUri: Uri? = null
    private var files: FileIndex? = null
    private var currentIdx = 0
    private var currentUri: Uri? = null
    private var scrollPos = 0.0
    @Volatile private var showGen = 0
    @Volatile private var scanGen = 0
    @Volatile private var searchGen = 0
    private var viewerLive = false

    private val cToolbar = Color.parseColor("#F0F0F0")
    private val cNav = Color.parseColor("#EEEEEE")
    private val cFg = Color.parseColor("#111111")
    private val cMuted = Color.parseColor("#888888")
    private val cDark = Color.parseColor("#222222")
    private val cGreen = Color.parseColor("#2D7A2D")
    private val cOrange = Color.parseColor("#E07700")
    private val cRed = Color.parseColor("#B00020")
    private val cStroke = Color.parseColor("#DDDDDD")

    private lateinit var rootView: LinearLayout
    private lateinit var listPanel: LinearLayout
    private lateinit var listView: ListView
    private lateinit var adapter: FilesAdapter
    private lateinit var viewer: TextCanvas
    private lateinit var vbar: VScrollBar
    private lateinit var btnOpen: Button
    private lateinit var btnRefresh: Button
    private lateinit var btnCopy: Button
    private lateinit var btnSearch: Button
    private lateinit var btnClear: Button
    private lateinit var btnPrev: Button
    private lateinit var btnNext: Button
    private lateinit var searchEdit: EditText
    private lateinit var lblFile: TextView
    private lateinit var lblAutocopy: TextView
    private lateinit var lblCount: TextView
    private lateinit var lblSearchStatus: TextView
    private lateinit var lblNav: TextView
    private lateinit var lblLnCol: TextView
    private lateinit var lblLines: TextView
    private lateinit var lblTotal: TextView
    private lateinit var lblSel: TextView
    private lateinit var lblLoading: TextView

    private val saveRun = Runnable { saveState() }
    private val hideAutocopyRun = Runnable { lblAutocopy.text = "" }

    private fun dp(v: Int): Int = (v * resources.displayMetrics.density + 0.5f).toInt()

    private fun lp(w: Int, h: Int, wt: Float): LinearLayout.LayoutParams = LinearLayout.LayoutParams(w, h, wt)

    private fun roundBg(fill: Int, stroke: Int): GradientDrawable {
        val g = GradientDrawable()
        g.setColor(fill)
        g.cornerRadius = dp(6).toFloat()
        g.setStroke(dp(1), stroke)
        return g
    }

    private fun mkBtn(text: String, dark: Boolean, onClick: () -> Unit): Button {
        val b = Button(this)
        b.text = text
        b.isAllCaps = false
        b.isFocusable = false
        b.isFocusableInTouchMode = false
        b.setTextColor(if (dark) Color.WHITE else cFg)
        b.textSize = 13f
        b.typeface = Typeface.DEFAULT_BOLD
        b.background = roundBg(if (dark) cDark else cToolbar, if (dark) cDark else cStroke)
        b.setPadding(dp(8), dp(4), dp(8), dp(4))
        b.minHeight = 0
        b.minimumHeight = dp(40)
        b.stateListAnimator = null
        b.setOnClickListener { onClick() }
        return b
    }

    private fun tv(text: String, size: Float, color: Int, bold: Boolean): TextView {
        val t = TextView(this)
        t.text = text
        t.textSize = size
        t.setTextColor(color)
        if (bold) t.typeface = Typeface.DEFAULT_BOLD
        return t
    }

    private fun divider(color: Int, horizontal: Boolean): View {
        val v = View(this)
        v.setBackgroundColor(color)
        v.layoutParams = if (horizontal) LinearLayout.LayoutParams(MATCH, 1) else LinearLayout.LayoutParams(1, MATCH)
        return v
    }

    private fun sep(): TextView {
        val t = tv("│", 11f, Color.parseColor("#CCCCCC"), false)
        t.setPadding(dp(6), 0, dp(6), 0)
        return t
    }

    private fun listWidthPx(): Int = dp(if (resources.configuration.screenWidthDp >= 600) 200 else 130)

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        window.setSoftInputMode(WindowManager.LayoutParams.SOFT_INPUT_STATE_ALWAYS_HIDDEN or WindowManager.LayoutParams.SOFT_INPUT_ADJUST_RESIZE)
        prefs = getSharedPreferences("text_browser_state", Context.MODE_PRIVATE)
        currentIdx = prefs.getInt("current_idx", 0)
        scrollPos = prefs.getString("scroll_pos", "0.0")?.toDoubleOrNull() ?: 0.0
        val fs = prefs.getString("folder", "") ?: ""
        if (fs.isNotEmpty()) folderUri = Uri.parse(fs)
        buildUi()
        val fu = folderUri
        if (fu != null && hasPermission(fu)) loadFolder(true, null, false)
    }

    private fun hasPermission(u: Uri): Boolean {
        for (p in contentResolver.persistedUriPermissions) {
            if (p.uri == u && p.isReadPermission) return true
        }
        return false
    }

    private fun buildUi() {
        val root = LinearLayout(this)
        root.orientation = LinearLayout.VERTICAL
        root.setBackgroundColor(Color.WHITE)
        root.isFocusableInTouchMode = true
        rootView = root

        // ── top toolbar (equal-weight buttons, status text under them) ──
        val bar = LinearLayout(this)
        bar.orientation = LinearLayout.VERTICAL
        bar.setBackgroundColor(cToolbar)
        bar.setPadding(dp(10), dp(8), dp(10), dp(6))
        val row1 = LinearLayout(this)
        row1.orientation = LinearLayout.HORIZONTAL
        btnOpen = mkBtn("Open Folder", true) { openFolderPicker() }
        btnRefresh = mkBtn("↻  Refresh", false) { refreshFolder() }
        btnCopy = mkBtn("⎘  Copy All Text", false) { copyAllText() }
        for (b in listOf(btnOpen, btnRefresh, btnCopy)) {
            val l = lp(0, WRAP, 1f)
            l.setMargins(dp(2), 0, dp(2), 0)
            row1.addView(b, l)
        }
        bar.addView(row1, lp(MATCH, WRAP, 0f))
        val row2 = LinearLayout(this)
        row2.orientation = LinearLayout.HORIZONTAL
        row2.gravity = Gravity.CENTER_VERTICAL
        row2.setPadding(0, dp(6), 0, 0)
        lblFile = tv("No folder loaded", 12f, cMuted, false)
        lblFile.gravity = Gravity.CENTER
        lblFile.setSingleLine(true)
        lblFile.ellipsize = TextUtils.TruncateAt.MIDDLE
        lblAutocopy = tv("", 12f, cGreen, true)
        lblAutocopy.setPadding(dp(6), 0, dp(6), 0)
        lblCount = tv("", 11f, cMuted, false)
        row2.addView(lblFile, lp(0, WRAP, 1f))
        row2.addView(lblAutocopy, lp(WRAP, WRAP, 0f))
        row2.addView(lblCount, lp(WRAP, WRAP, 0f))
        bar.addView(row2, lp(MATCH, WRAP, 0f))
        root.addView(bar, lp(MATCH, WRAP, 0f))

        // ── search bar ──
        val sbar = LinearLayout(this)
        sbar.orientation = LinearLayout.VERTICAL
        sbar.setBackgroundColor(cToolbar)
        sbar.setPadding(dp(10), 0, dp(10), dp(6))
        val srow = LinearLayout(this)
        srow.orientation = LinearLayout.HORIZONTAL
        srow.gravity = Gravity.CENTER_VERTICAL
        srow.addView(tv("🔎", 14f, cMuted, false), lp(WRAP, WRAP, 0f))
        searchEdit = EditText(this)
        searchEdit.setSingleLine(true)
        searchEdit.textSize = 14f
        searchEdit.setTextColor(cFg)
        searchEdit.background = roundBg(Color.WHITE, cStroke)
        searchEdit.setPadding(dp(8), dp(6), dp(8), dp(6))
        searchEdit.imeOptions = EditorInfo.IME_ACTION_SEARCH
        searchEdit.setOnEditorActionListener { _, actionId, ev ->
            if (actionId == EditorInfo.IME_ACTION_SEARCH || (ev != null && ev.keyCode == KeyEvent.KEYCODE_ENTER && ev.action == KeyEvent.ACTION_DOWN)) {
                startSearch()
                true
            } else {
                false
            }
        }
        val el = lp(0, WRAP, 1f)
        el.setMargins(dp(6), 0, dp(6), 0)
        srow.addView(searchEdit, el)
        btnSearch = mkBtn("Search", true) { startSearch() }
        btnClear = mkBtn("✕", false) { clearSearch() }
        val bl = lp(WRAP, WRAP, 0f)
        bl.setMargins(0, 0, dp(4), 0)
        srow.addView(btnSearch, bl)
        srow.addView(btnClear, lp(WRAP, WRAP, 0f))
        sbar.addView(srow, lp(MATCH, WRAP, 0f))
        lblSearchStatus = tv("", 11f, cMuted, false)
        lblSearchStatus.visibility = View.GONE
        lblSearchStatus.setPadding(dp(4), dp(4), 0, 0)
        sbar.addView(lblSearchStatus, lp(MATCH, WRAP, 0f))
        root.addView(sbar, lp(MATCH, WRAP, 0f))
        root.addView(divider(Color.parseColor("#CCCCCC"), true))

        // ── main area: file list | viewer ──
        val main = LinearLayout(this)
        main.orientation = LinearLayout.HORIZONTAL
        listPanel = LinearLayout(this)
        listPanel.orientation = LinearLayout.VERTICAL
        listPanel.setBackgroundColor(Color.parseColor("#F8F8F8"))
        val hdr = tv("FILES", 11f, cMuted, true)
        hdr.setPadding(dp(10), dp(6), dp(10), dp(6))
        listPanel.addView(hdr, lp(MATCH, WRAP, 0f))
        listPanel.addView(divider(cStroke, true))
        listView = ListView(this)
        listView.setBackgroundColor(Color.parseColor("#F8F8F8"))
        listView.divider = null
        listView.dividerHeight = 0
        listView.isFastScrollEnabled = true
        listView.isFocusable = false
        listView.setSelector(android.R.color.transparent)
        adapter = FilesAdapter()
        listView.adapter = adapter
        listView.setOnItemClickListener { _, _, position, _ ->
            scrollPos = 0.0
            showFile(position, false, true, null, -1L)
        }
        listPanel.addView(listView, lp(MATCH, 0, 1f))
        main.addView(listPanel, lp(listWidthPx(), MATCH, 0f))
        main.addView(divider(Color.parseColor("#CCCCCC"), false))
        val vbox = LinearLayout(this)
        vbox.orientation = LinearLayout.HORIZONTAL
        viewer = TextCanvas(this)
        vbar = VScrollBar(this)
        vbox.addView(viewer, lp(0, MATCH, 1f))
        vbox.addView(vbar, lp(dp(22), MATCH, 0f))
        main.addView(vbox, lp(0, MATCH, 1f))
        root.addView(main, lp(MATCH, 0, 1f))

        // ── notepad-style status bar ──
        val st = LinearLayout(this)
        st.orientation = LinearLayout.VERTICAL
        st.setBackgroundColor(cNav)
        st.addView(divider(Color.parseColor("#CCCCCC"), true))
        val sa = LinearLayout(this)
        sa.orientation = LinearLayout.HORIZONTAL
        sa.setPadding(dp(10), dp(3), dp(10), 0)
        lblLnCol = tv("Ln 1, Col 1", 11f, cMuted, false)
        lblLines = tv("Lines: 0", 11f, cMuted, false)
        lblTotal = tv("Characters: 0", 11f, cMuted, false)
        sa.addView(lblLnCol)
        sa.addView(sep())
        sa.addView(lblLines)
        sa.addView(sep())
        sa.addView(lblTotal)
        st.addView(sa, lp(MATCH, WRAP, 0f))
        val sbb = LinearLayout(this)
        sbb.orientation = LinearLayout.HORIZONTAL
        sbb.setPadding(dp(10), 0, dp(10), dp(3))
        lblSel = tv("", 11f, cMuted, false)
        lblLoading = tv("", 11f, cOrange, true)
        sbb.addView(lblSel, lp(0, WRAP, 1f))
        sbb.addView(lblLoading, lp(WRAP, WRAP, 0f))
        st.addView(sbb, lp(MATCH, WRAP, 0f))
        root.addView(st, lp(MATCH, WRAP, 0f))

        // ── navigation bar ──
        val nav = LinearLayout(this)
        nav.orientation = LinearLayout.HORIZONTAL
        nav.gravity = Gravity.CENTER_VERTICAL
        nav.setBackgroundColor(cNav)
        nav.setPadding(dp(10), dp(8), dp(10), dp(8))
        btnPrev = mkBtn("◀  Previous", false) { prevFile() }
        btnNext = mkBtn("Next  ▶", false) { nextFile() }
        btnPrev.textSize = 14f
        btnNext.textSize = 14f
        lblNav = tv("", 11f, cMuted, false)
        lblNav.gravity = Gravity.CENTER
        nav.addView(btnPrev, lp(0, WRAP, 1f))
        nav.addView(lblNav, lp(0, WRAP, 1f))
        nav.addView(btnNext, lp(0, WRAP, 1f))
        root.addView(nav, lp(MATCH, WRAP, 0f))

        setContentView(root)
        root.requestFocus()

        viewer.onScrolled = { onViewerScrolled() }
        viewer.onSelection = { updateStatus() }
        viewer.onCaret = { updateStatus() }
        viewer.onContextMenu = { showContextMenu() }
        viewer.onTouched = { hideKeyboardOnly() }
        vbar.onDrag = { p ->
            viewer.jumpToFraction(p)
            onViewerScrolled()
        }
        updateStatus()
    }

    override fun onConfigurationChanged(newConfig: Configuration) {
        super.onConfigurationChanged(newConfig)
        val l = listPanel.layoutParams
        l.width = listWidthPx()
        listPanel.layoutParams = l
    }

    inner class FilesAdapter : BaseAdapter() {
        override fun getCount(): Int {
            val fi = files
            return if (fi == null) 0 else fi.size
        }

        override fun getItem(position: Int): Any = position

        override fun getItemId(position: Int): Long = position.toLong()

        override fun getView(position: Int, convertView: View?, parent: ViewGroup?): View {
            val t: TextView
            if (convertView is TextView) {
                t = convertView
            } else {
                t = TextView(this@MainActivity)
                t.textSize = 12f
                t.setSingleLine(true)
                t.ellipsize = TextUtils.TruncateAt.END
                t.gravity = Gravity.CENTER_VERTICAL
                t.setPadding(dp(10), 0, dp(6), 0)
                t.layoutParams = AbsListView.LayoutParams(MATCH, dp(36))
            }
            val fi = files
            t.text = if (fi != null && position < fi.size) fi.name(position) else ""
            if (position == currentIdx) {
                t.setBackgroundColor(cDark)
                t.setTextColor(Color.WHITE)
            } else {
                t.setBackgroundColor(Color.parseColor("#F8F8F8"))
                t.setTextColor(cFg)
            }
            return t
        }
    }

    // ───────── state ─────────
    private fun saveState() {
        prefs.edit()
            .putString("folder", folderUri?.toString() ?: "")
            .putInt("current_idx", currentIdx)
            .putString("scroll_pos", scrollPos.toString())
            .apply()
    }

    private fun scheduleSave() {
        uiHandler.removeCallbacks(saveRun)
        uiHandler.postDelayed(saveRun, 600)
    }

    override fun onPause() {
        super.onPause()
        if (viewerLive) scrollPos = viewer.scrollFraction()
        saveState()
    }

    override fun onDestroy() {
        super.onDestroy()
        searchGen++
        scanGen++
        showGen++
        viewer.release()
    }

    private fun alertBox(title: String, msg: String) {
        AlertDialog.Builder(this).setTitle(title).setMessage(msg).setPositiveButton("OK", null).show()
    }

    private fun hideKeyboardOnly() {
        try {
            val imm = getSystemService(Context.INPUT_METHOD_SERVICE) as InputMethodManager
            imm.hideSoftInputFromWindow(searchEdit.windowToken, 0)
        } catch (ex: Throwable) { }
    }

    private fun hideKeyboard() {
        hideKeyboardOnly()
        rootView.requestFocus()
    }

    // ───────── status / header ─────────
    private fun onViewerScrolled() {
        vbar.set(viewer.scrollFraction(), viewer.visibleFraction())
        if (viewerLive) {
            scrollPos = viewer.scrollFraction()
            scheduleSave()
        }
    }

    private fun updateStatus() {
        lblLnCol.text = "Ln " + viewer.caretLn + ", Col " + viewer.caretCol
        val di = viewer.docIndex
        if (di == null) {
            lblLines.text = "Lines: 0"
            lblTotal.text = "Characters: 0"
        } else if (di.done) {
            lblLines.text = "Lines: " + fmt(di.totalLines)
            lblTotal.text = "Characters: " + fmt(di.totalChars)
        } else {
            lblLines.text = "Lines: …"
            lblTotal.text = "Characters: …"
        }
        val r = viewer.selectionRange()
        if (r == null) {
            lblSel.text = ""
        } else if (di != null && di.done) {
            val hi = if (r[1] > di.totalChars) di.totalChars else r[1]
            val n = if (hi - r[0] > 0L) hi - r[0] else 0L
            lblSel.text = "Selected: " + fmt(n) + " character" + (if (n != 1L) "s" else "")
        } else if (r[1] > 4000000000000L) {
            lblSel.text = "Selected: all text"
        } else {
            val n = r[1] - r[0]
            lblSel.text = "Selected: " + fmt(n) + " character" + (if (n != 1L) "s" else "")
        }
    }

    private fun updateHeader() {
        val fi = files
        if (fi == null || fi.size == 0 || currentIdx >= fi.size) return
        val name = fi.name(currentIdx)
        lblFile.text = name
        title = "Text Browser  —  " + name
        lblNav.text = "" + (currentIdx + 1) + "  /  " + fi.size
        btnPrev.isEnabled = currentIdx > 0
        btnPrev.alpha = if (currentIdx > 0) 1f else 0.4f
        btnNext.isEnabled = currentIdx < fi.size - 1
        btnNext.alpha = if (currentIdx < fi.size - 1) 1f else 0.4f
    }

    private fun ensureListVisible(idx: Int) {
        if (idx < listView.firstVisiblePosition || idx > listView.lastVisiblePosition) {
            listView.setSelectionFromTop(idx, listView.height / 3)
        }
    }

    private fun showAutoCopy(msg: String) {
        lblAutocopy.text = msg
        uiHandler.removeCallbacks(hideAutocopyRun)
        uiHandler.postDelayed(hideAutocopyRun, 1500)
    }

    private fun setSearchStatus(text: String, color: Int) {
        lblSearchStatus.text = text
        lblSearchStatus.setTextColor(color)
        lblSearchStatus.visibility = if (text.isEmpty()) View.GONE else View.VISIBLE
    }

    private fun flashButton(b: Button, doneText: String, origText: String, origBg: Int, origFg: Int, origStroke: Int) {
        b.text = doneText
        b.background = roundBg(cGreen, cGreen)
        b.setTextColor(Color.WHITE)
        uiHandler.postDelayed({
            b.text = origText
            b.background = roundBg(origBg, origStroke)
            b.setTextColor(origFg)
        }, 1200)
    }

    // ───────── folder handling ─────────
    private fun openFolderPicker() {
        val i = Intent(Intent.ACTION_OPEN_DOCUMENT_TREE)
        i.addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION or Intent.FLAG_GRANT_PERSISTABLE_URI_PERMISSION)
        startActivityForResult(i, 1001)
    }

    override fun onActivityResult(requestCode: Int, resultCode: Int, data: Intent?) {
        super.onActivityResult(requestCode, resultCode, data)
        if (requestCode == 1001 && resultCode == RESULT_OK) {
            val u = data?.data ?: return
            try {
                contentResolver.takePersistableUriPermission(u, Intent.FLAG_GRANT_READ_URI_PERMISSION)
            } catch (ex: Throwable) { }
            folderUri = u
            currentIdx = 0
            scrollPos = 0.0
            saveState()
            loadFolder(false, null, false)
        }
    }

    private fun refreshFolder() {
        if (folderUri == null) {
            alertBox("No Folder", "Please open a folder first.")
            return
        }
        val fi = files
        val cur = if (fi != null && fi.size > 0 && currentIdx < fi.size) fi.name(currentIdx) else null
        loadFolder(false, cur, true)
    }

    private fun loadFolder(restore: Boolean, keep: String?, isRefresh: Boolean) {
        val tree = folderUri ?: return
        val gen = ++scanGen
        lblLoading.text = "Scanning…"
        lblCount.text = ""
        if (restore) {
            val th = Thread {
                val cached = IndexCache.load(this, tree.toString())
                val csig = if (cached != null) cached.signature() else 0L
                runOnUiThread {
                    if (gen == scanGen) {
                        if (cached != null && cached.size > 0) {
                            applyFileIndex(cached, true, null, false)
                            startScan(tree, gen, true, null, false, true, csig)
                        } else {
                            startScan(tree, gen, true, null, false, false, 0L)
                        }
                    }
                }
            }
            th.isDaemon = true
            th.start()
        } else {
            startScan(tree, gen, false, keep, isRefresh, false, 0L)
        }
    }

    private fun startScan(tree: Uri, gen: Int, restore: Boolean, keep: String?, isRefresh: Boolean, silent: Boolean, cachedSig: Long) {
        val th = Thread {
            var res: FileIndex? = null
            var err: String? = null
            try {
                res = scanFolder(contentResolver, tree, { n ->
                    if (!silent) runOnUiThread { if (gen == scanGen) lblLoading.text = "Scanning… " + fmt(n.toLong()) }
                }, { gen != scanGen })
            } catch (ex: Throwable) {
                err = ex.message ?: ex.toString()
            }
            val r = res
            val e = err
            var sig = 0L
            if (r != null && r.size > 0 && gen == scanGen) {
                sig = r.signature()
                if (!silent || sig != cachedSig) IndexCache.save(this, tree.toString(), r)
            }
            runOnUiThread { onScanDone(gen, r, e, restore, keep, isRefresh, silent, cachedSig, sig) }
        }
        th.isDaemon = true
        th.start()
    }

    private fun onScanDone(gen: Int, r: FileIndex?, err: String?, restore: Boolean, keep: String?, isRefresh: Boolean, silent: Boolean, cachedSig: Long, sig: Long) {
        if (gen != scanGen) return
        if (err != null) {
            if (!silent) {
                lblLoading.text = ""
                alertBox("Error", err)
            }
            return
        }
        if (r == null) return
        if (r.size == 0) {
            if (!silent) {
                lblLoading.text = ""
                alertBox("Empty", "No .txt files found in that folder.")
            }
            return
        }
        if (silent) {
            if (sig != cachedSig) swapIndexSilently(r)
            return
        }
        applyFileIndex(r, restore, keep, isRefresh)
    }

    private fun swapIndexSilently(r: FileIndex) {
        val old = files
        val curName = if (old != null && currentIdx < old.size) old.name(currentIdx) else null
        files = r
        adapter.notifyDataSetChanged()
        lblCount.text = fmt(r.size.toLong()) + " files"
        val ni = if (curName != null) r.indexOf(curName) else -1
        if (ni >= 0) {
            currentIdx = ni
            updateHeader()
            ensureListVisible(ni)
        } else {
            showFile(if (currentIdx < r.size) currentIdx else r.size - 1, false, false, null, -1L)
        }
    }

    private fun applyFileIndex(fi: FileIndex, restore: Boolean, keep: String?, isRefresh: Boolean) {
        files = fi
        val n = fi.size
        lblCount.text = fmt(n.toLong()) + " files"
        lblLoading.text = ""
        var targetIdx: Int
        var targetScroll = 0.0
        if (restore) {
            targetIdx = prefs.getInt("current_idx", 0)
            if (targetIdx > n - 1) targetIdx = n - 1
            targetScroll = prefs.getString("scroll_pos", "0.0")?.toDoubleOrNull() ?: 0.0
        } else {
            val k = if (keep != null) fi.indexOf(keep) else -1
            if (k >= 0) {
                targetIdx = k
            } else {
                targetIdx = if (currentIdx < n - 1) currentIdx else n - 1
            }
        }
        if (targetIdx < 0) targetIdx = 0
        adapter.notifyDataSetChanged()
        scrollPos = targetScroll
        showFile(targetIdx, restore, false, null, -1L)
        listView.post { ensureListVisible(targetIdx) }
        if (isRefresh) flashButton(btnRefresh, "✓  Refreshed!", "↻  Refresh", cToolbar, cFg, cStroke)
    }

    // ───────── showing a file ─────────
    private fun prevFile() {
        if (files != null && currentIdx > 0) {
            scrollPos = 0.0
            showFile(currentIdx - 1, false, false, null, -1L)
        }
    }

    private fun nextFile() {
        val fi = files ?: return
        if (currentIdx < fi.size - 1) {
            scrollPos = 0.0
            showFile(currentIdx + 1, false, false, null, -1L)
        }
    }

    private fun showFile(idx0: Int, restoreScroll: Boolean, autoCopy: Boolean, searchTerm: String?, searchOffset: Long) {
        val fi = files ?: return
        if (fi.size == 0) return
        val tree = folderUri ?: return
        val idx = if (idx0 < 0) 0 else if (idx0 >= fi.size) fi.size - 1 else idx0
        currentIdx = idx
        val gen = ++showGen
        viewerLive = false
        viewer.showMessage("Loading…")
        lblLoading.text = "Reading file…"
        updateHeader()
        updateStatus()
        saveState()
        adapter.notifyDataSetChanged()
        ensureListVisible(idx)
        val uri = DocumentsContract.buildDocumentUriUsingTree(tree, fi.docId(idx))
        currentUri = uri
        val restoreFrac = if (restoreScroll) scrollPos else 0.0
        val th = Thread {
            var src: TextSource? = null
            var di: DocIndex? = null
            var err: String? = null
            try {
                val s = TextSource.open(contentResolver, uri)
                src = s
                val d = DocIndex()
                if (s.size <= SYNC_INDEX_LIMIT) buildDocIndex(s, d, { gen != showGen }, { })
                di = d
            } catch (ex: Throwable) {
                err = "[Could not read file: " + (ex.message ?: ex.toString()) + "]"
                if (src != null) src.close()
                src = null
                di = null
            }
            val fs = src
            val fd = di
            val fe = err
            runOnUiThread {
                if (gen != showGen) {
                    if (fs != null) fs.close()
                } else if (fs == null || fd == null) {
                    viewer.showMessage(fe ?: "[Could not read file]")
                    lblLoading.text = ""
                    updateStatus()
                } else {
                    viewer.attach(fs, fd)
                    viewer.setHighlight(searchTerm)
                    val hasJump = searchOffset >= 0L || (restoreScroll && restoreFrac > 0.0)
                    if (fd.done) {
                        lblLoading.text = ""
                        if (searchOffset >= 0L) {
                            viewer.jumpToOffset(searchOffset, true)
                        } else if (restoreScroll && restoreFrac > 0.0) {
                            viewer.jumpToFraction(restoreFrac)
                        }
                        viewerLive = true
                    } else {
                        if (searchOffset >= 0L) {
                            viewer.setPending(searchOffset, -1.0, true)
                        } else if (restoreScroll && restoreFrac > 0.0) {
                            viewer.setPending(-1L, restoreFrac, false)
                        }
                        viewerLive = !hasJump
                        lblLoading.text = "Indexing…"
                        startIndexThread(fs, fd, gen)
                    }
                    updateStatus()
                    onViewerScrolled()
                    if (autoCopy) doAutoCopy(uri, gen)
                }
            }
        }
        th.isDaemon = true
        th.start()
    }

    private fun startIndexThread(s: TextSource, d: DocIndex, gen: Int) {
        val th = Thread {
            var lastPost = 0L
            val ok = try {
                buildDocIndex(s, d, { gen != showGen || s.closed }, { p ->
                    val now = System.nanoTime()
                    if (now - lastPost > 200000000L) {
                        lastPost = now
                        val pct = if (s.size > 0L) (p * 100L / s.size).toInt() else 0
                        runOnUiThread { if (gen == showGen) lblLoading.text = "Indexing… " + pct + "%" }
                    }
                })
            } catch (ex: Throwable) {
                false
            }
            if (ok) runOnUiThread { if (gen == showGen) onIndexDone() }
        }
        th.isDaemon = true
        th.start()
    }

    private fun onIndexDone() {
        lblLoading.text = ""
        viewer.applyPending()
        viewerLive = true
        updateStatus()
        onViewerScrolled()
    }

    // ───────── clipboard ─────────
    private fun setClip(text: String): Boolean {
        return try {
            val cm = getSystemService(Context.CLIPBOARD_SERVICE) as ClipboardManager
            cm.setPrimaryClip(ClipData.newPlainText("text", text))
            true
        } catch (ex: Throwable) {
            false
        }
    }

    // Android's clipboard cannot hold GB of text, so at most CLIP_MAX characters are copied.
    private fun readHead(uri: Uri): Pair<String, Boolean>? {
        var s: TextSource? = null
        try {
            val src = TextSource.open(contentResolver, uri)
            s = src
            val maxBytes = CLIP_MAX.toLong() * 4L + 16L
            val want = (if (src.size < maxBytes) src.size else maxBytes).toInt()
            val buf = ByteArray(want)
            val n = src.readFully(0L, buf, 0, want)
            if (n <= 0) return null
            var truncated = src.size > maxBytes
            var text = String(buf, 0, n, Charsets.UTF_8)
            text = text.replace("\r\n", "\n").replace('\r', '\n')
            if (text.length > CLIP_MAX) {
                var cut = CLIP_MAX
                if (Character.isHighSurrogate(text[cut - 1])) cut--
                text = text.substring(0, cut)
                truncated = true
            }
            return Pair(text, truncated)
        } catch (ex: Throwable) {
            return null
        } finally {
            if (s != null) s.close()
        }
    }

    private fun truncMsg(): String = "✓ Copied first " + fmt(CLIP_MAX.toLong()) + " characters"

    private fun doAutoCopy(uri: Uri, gen: Int) {
        val th = Thread {
            val r = readHead(uri)
            runOnUiThread {
                if (r != null && gen == showGen && r.first.isNotBlank()) {
                    if (setClip(r.first)) showAutoCopy(if (r.second) truncMsg() else "✓ Copied to clipboard")
                }
            }
        }
        th.isDaemon = true
        th.start()
    }

    private fun copyAllText() {
        val uri = currentUri ?: return
        if (!viewerLive && viewer.currentSource() == null) return
        val th = Thread {
            val r = readHead(uri)
            runOnUiThread {
                if (r != null && r.first.isNotBlank()) {
                    if (setClip(r.first)) {
                        flashButton(btnCopy, "✓  Copied!", "⎘  Copy All Text", cToolbar, cFg, cStroke)
                        if (r.second) Toast.makeText(this, "File is large: copied first " + fmt(CLIP_MAX.toLong()) + " characters", Toast.LENGTH_LONG).show()
                    }
                }
            }
        }
        th.isDaemon = true
        th.start()
    }

    private fun copySelection() {
        val r = viewer.selectionRange()
        if (r == null) {
            Toast.makeText(this, "Nothing selected", Toast.LENGTH_SHORT).show()
            return
        }
        val s = viewer.currentSource() ?: return
        val di = viewer.docIndex
        val th = Thread {
            val res = extractRange(s, di, r[0], r[1], CLIP_MAX)
            runOnUiThread {
                if (res.first.isNotEmpty()) {
                    if (setClip(res.first)) showAutoCopy(if (res.second) truncMsg() else "✓ Copied to clipboard")
                }
            }
        }
        th.isDaemon = true
        th.start()
    }

    private fun selectAll() {
        val di = viewer.docIndex
        val total = if (di != null && di.done) di.totalChars else Long.MAX_VALUE / 4L
        viewer.selectAll(total)
        updateStatus()
    }

    private fun showContextMenu() {
        val items = arrayOf("Copy", "Select All", "Copy All Text")
        AlertDialog.Builder(this).setItems(items) { _, which ->
            when (which) {
                0 -> copySelection()
                1 -> selectAll()
                2 -> copyAllText()
                else -> { }
            }
        }.show()
    }

    // ───────── content search across all files ─────────
    private fun startSearch() {
        val term = searchEdit.text.toString().trim()
        if (term.isEmpty()) return
        val tree = folderUri
        if (tree == null) {
            alertBox("No Folder", "Please open a folder first.")
            return
        }
        val fi = files
        if (fi == null || fi.size == 0) {
            alertBox("No Files", "There are no .txt files to search.")
            return
        }
        hideKeyboard()
        val myGen = ++searchGen
        btnSearch.isEnabled = false
        setSearchStatus("Searching for “" + term + "”…", cOrange)
        val needle = term.lowercase()
        val th = Thread {
            val n = fi.size
            val next = AtomicInteger(0)
            val done = AtomicInteger(0)
            val lock = Any()
            val bestIdx = intArrayOf(Int.MAX_VALUE)
            val bestOff = longArrayOf(-1L)
            val workers = ArrayList<Thread>()
            for (w in 0 until 4) {
                val wt = Thread {
                    val buf = ByteArray(1 shl 20)
                    while (true) {
                        if (searchGen != myGen) break
                        val i = next.getAndIncrement()
                        if (i >= n) break
                        val cur = synchronized(lock) { bestIdx[0] }
                        if (i >= cur) break
                        val off = try {
                            val u = DocumentsContract.buildDocumentUriUsingTree(tree, fi.docId(i))
                            searchFile(u, needle, buf, { searchGen != myGen })
                        } catch (ex: Throwable) {
                            -1L
                        }
                        if (off >= 0L) {
                            synchronized(lock) {
                                if (i < bestIdx[0]) {
                                    bestIdx[0] = i
                                    bestOff[0] = off
                                }
                            }
                        }
                        val c = done.incrementAndGet()
                        if (c % 25 == 0) {
                            runOnUiThread {
                                if (searchGen == myGen) setSearchStatus("Searching… " + fmt(c.toLong()) + "/" + fmt(n.toLong()) + " files", cOrange)
                            }
                        }
                    }
                }
                wt.isDaemon = true
                wt.start()
                workers.add(wt)
            }
            for (wt in workers) wt.join()
            if (searchGen == myGen) {
                val bi = bestIdx[0]
                val bo = bestOff[0]
                runOnUiThread {
                    if (searchGen == myGen) onSearchDone(term, if (bi == Int.MAX_VALUE) -1 else bi, bo)
                }
            }
        }
        th.isDaemon = true
        th.start()
    }

    // Returns byte offset of the first case-insensitive match, -1 if none, -2 if cancelled.
    private fun searchFile(uri: Uri, needle: String, buf: ByteArray, cancelled: () -> Boolean): Long {
        val pfd = contentResolver.openFileDescriptor(uri, "r") ?: return -1L
        try {
            val ch = FileInputStream(pfd.fileDescriptor).channel
            val size = ch.size()
            var pos = 0L
            while (pos < size) {
                if (cancelled()) return -2L
                val remain = size - pos
                val want = if (remain < buf.size.toLong()) remain.toInt() else buf.size
                val bb = ByteBuffer.wrap(buf, 0, want)
                var got = 0
                while (bb.hasRemaining()) {
                    val r = ch.read(bb, pos + got)
                    if (r <= 0) break
                    got += r
                }
                if (got <= 0) break
                var cut = got
                if (pos + got < size) {
                    var k = got - 1
                    while (k >= 0 && buf[k] != NL) k--
                    if (k >= 0) {
                        cut = k + 1
                    } else {
                        while (cut > 0 && (buf[cut - 1].toInt() and 0xC0) == 0x80) cut--
                        if (cut > 0 && (buf[cut - 1].toInt() and 0x80) != 0) cut--
                        if (cut <= 0) cut = got
                    }
                }
                val orig = String(buf, 0, cut, Charsets.UTF_8)
                val idx = orig.lowercase().indexOf(needle)
                if (idx >= 0) {
                    val e = if (idx < orig.length) idx else orig.length
                    return pos + orig.substring(0, e).toByteArray(Charsets.UTF_8).size
                }
                pos += cut
            }
            return -1L
        } finally {
            try { pfd.close() } catch (ex: Throwable) { }
        }
    }

    private fun onSearchDone(term: String, idx: Int, off: Long) {
        btnSearch.isEnabled = true
        val fi = files ?: return
        if (idx < 0 || idx >= fi.size) {
            setSearchStatus("No match found for “" + term + "”", cRed)
            return
        }
        setSearchStatus("Found in: " + fi.name(idx), cGreen)
        scrollPos = 0.0
        showFile(idx, false, false, term, off)
    }

    private fun clearSearch() {
        searchGen++
        searchEdit.setText("")
        viewer.setHighlight(null)
        setSearchStatus("", cMuted)
        btnSearch.isEnabled = true
    }

    // ───────── keyboard shortcuts ─────────
    override fun dispatchKeyEvent(e: KeyEvent): Boolean {
        if (e.action != KeyEvent.ACTION_DOWN || searchEdit.hasFocus()) return super.dispatchKeyEvent(e)
        val ctrl = e.isCtrlPressed
        when (e.keyCode) {
            KeyEvent.KEYCODE_DPAD_LEFT -> { prevFile(); return true }
            KeyEvent.KEYCODE_DPAD_RIGHT -> { nextFile(); return true }
            KeyEvent.KEYCODE_DPAD_UP -> { viewer.scrollLines(-1); return true }
            KeyEvent.KEYCODE_DPAD_DOWN -> { viewer.scrollLines(1); return true }
            KeyEvent.KEYCODE_PAGE_UP -> { viewer.pageScroll(-1); return true }
            KeyEvent.KEYCODE_PAGE_DOWN -> { viewer.pageScroll(1); return true }
            KeyEvent.KEYCODE_MOVE_HOME -> { viewer.goTop(); return true }
            KeyEvent.KEYCODE_MOVE_END -> { viewer.goBottom(); return true }
            KeyEvent.KEYCODE_A -> {
                if (ctrl) {
                    selectAll()
                    return true
                }
            }
            KeyEvent.KEYCODE_C -> {
                if (ctrl) {
                    copySelection()
                } else if (!viewer.hasFocus()) {
                    copyAllText()
                }
                return true
            }
            else -> { }
        }
        return super.dispatchKeyEvent(e)
    }
}
