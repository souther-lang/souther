package souther.compiler.cst;

import souther.compiler.diag.SourcePos;
import souther.compiler.diag.TextRead;

import java.util.ArrayList;
import java.util.List;

/**
 * Maps an absolute character offset to a line/column and back. The CST works in offsets (what
 * green widths accumulate to); diagnostics and the LSP need line/column. This is the one place
 * the two coordinate systems meet.
 *
 * <p>Lines and columns are 1-based for {@link SourcePos} (the compiler's convention); the LSP
 * accessors return 0-based positions. Columns count UTF-16 code units, which matches both Java
 * {@code char} offsets and the LSP's default position encoding.
 *
 * <p>An index made for a named source gives every {@link SourcePos} that source. This is the one
 * place a position is made from a text, so it is the one place that has both halves to hand — which
 * is why nothing downstream has to work the file out again from what it is looking at.
 */
public final class LineIndex {

    private final String source;
    /** What this is an index of, so that every position it makes says which source it is in and
     * whether that is where the code is. Both come from here because this is the one place a
     * position is made from a text, and neither is worked out again downstream. */
    private final TextRead read;
    /** {@code lineStart[i]} is the offset at which line {@code i} (0-based) begins. */
    private final int[] lineStart;

    /** An index of a text this caller has no name for — a reader that only wants offsets
     *  converted. Its positions name no source. */
    public LineIndex(String source) {
        this(source, TextRead.aTextWithNoIdentity());
    }

    /** An index of a file this compile holds, or of no named file when {@code sourceId} is null. */
    public LineIndex(String source, String sourceId) {
        this(source, sourceId == null ? TextRead.aTextWithNoIdentity()
                : TextRead.aFileOfThisCompile(sourceId));
    }

    public LineIndex(String source, TextRead read) {
        this.source = source;
        this.read = read;
        List<Integer> starts = new ArrayList<>();
        starts.add(0);
        for (int i = 0; i < source.length(); i++) {
            if (source.charAt(i) == '\n') {
                starts.add(i + 1);
            }
        }
        this.lineStart = new int[starts.size()];
        for (int i = 0; i < starts.size(); i++) {
            lineStart[i] = starts.get(i);
        }
    }

    /** The 1-based line containing {@code offset}. */
    public int lineOf(int offset) {
        return lineIndex(offset) + 1;
    }

    /** The 1-based column of {@code offset} within its line. */
    public int columnOf(int offset) {
        return offset - lineStart[lineIndex(offset)] + 1;
    }

    /** The compiler's 1-based line/column position for {@code offset}. */
    public SourcePos posOf(int offset) {
        int line = lineIndex(offset);
        return read.at(line + 1, offset - lineStart[line] + 1);
    }

    /** The 0-based line of {@code offset} (LSP). */
    public int lspLine(int offset) {
        return lineIndex(offset);
    }

    /** The 0-based column of {@code offset} within its line (LSP, UTF-16 units). */
    public int lspColumn(int offset) {
        return offset - lineStart[lineIndex(offset)];
    }

    /** The offset of a 0-based (line, column) LSP position, clamped into the source. */
    public int offsetOf(int lspLine, int lspColumn) {
        if (lspLine < 0) {
            return 0;
        }
        if (lspLine >= lineStart.length) {
            return source.length();
        }
        int base = lineStart[lspLine];
        int lineEnd = lspLine + 1 < lineStart.length ? lineStart[lspLine + 1] : source.length();
        return Math.min(base + Math.max(0, lspColumn), lineEnd);
    }

    private int lineIndex(int offset) {
        int lo = 0;
        int hi = lineStart.length - 1;
        while (lo < hi) {
            int mid = (lo + hi + 1) >>> 1;
            if (lineStart[mid] <= offset) {
                lo = mid;
            } else {
                hi = mid - 1;
            }
        }
        return lo;
    }
}
