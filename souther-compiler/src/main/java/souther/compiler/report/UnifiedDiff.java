package souther.compiler.report;

import java.util.ArrayList;
import java.util.List;

/**
 * Two texts and where they differ, in unified-diff form.
 *
 * <p>It reads the two texts and nothing else. What produced either of them, and which rule of
 * whatever produced them accounts for a line, is not a question this can answer and not one it is
 * asked: a caller that holds two texts holds the whole of what is rendered here.
 */
public final class UnifiedDiff {

    /** Unchanged lines kept on each side of a change, as {@code diff -u} keeps them. */
    private static final int CONTEXT = 3;

    /**
     * The largest table {@link #script} will build, in cells of one {@code int} — about sixteen
     * megabytes.
     *
     * <p>Which lines two texts share is answered by filling a table the size of one length times the
     * other, so a pair of texts large enough is a pair answered by exhausting the heap. Past this
     * size the differing part is shown whole: still the difference, and still one hunk of a unified
     * diff, but without saying which lines inside it the two had in common.
     */
    private static final long MAX_CELLS = 4_000_000L;

    private UnifiedDiff() {
    }

    /** One line of a text, and whether the text terminated it. Only the last line of a text can be
     * unterminated, and a text and the same text without its final newline are two texts: compared
     * as plain strings their lines are the same list, which leaves a difference with nothing to
     * show for it. */
    private record Line(String text, boolean terminated) {
    }

    private record Op(char kind, Line line) {
    }

    /**
     * The difference between {@code from} and {@code to}, or the empty string when they are the same
     * text. The labels name the two sides in the header and are written as given.
     */
    public static String of(String fromLabel, String toLabel, String from, String to) {
        if (from.equals(to)) {
            return "";
        }
        List<Line> a = lines(from);
        List<Line> b = lines(to);
        List<Op> ops = compare(a, b);
        StringBuilder out = new StringBuilder();
        out.append("--- ").append(fromLabel).append('\n');
        out.append("+++ ").append(toLabel).append('\n');
        render(ops, out);
        return out.toString();
    }

    private static List<Line> lines(String text) {
        List<Line> lines = new ArrayList<>();
        int start = 0;
        while (start < text.length()) {
            int end = text.indexOf('\n', start);
            if (end < 0) {
                lines.add(new Line(text.substring(start), false));
                return lines;
            }
            lines.add(new Line(text.substring(start, end), true));
            start = end + 1;
        }
        return lines;
    }

    /**
     * The whole edit script, with the lines the two texts already agree on at either end kept as
     * they are.
     *
     * <p>Only what is left between them is searched for common lines, which is what keeps the cost
     * of a file that is canonical everywhere but one place the cost of that one place. It is also
     * what {@link #MAX_CELLS} is measured against: a file past the bound overall but agreeing on all
     * but a few lines is the ordinary case, and it is not the case the bound is there for.
     */
    private static List<Op> compare(List<Line> a, List<Line> b) {
        int prefix = 0;
        while (prefix < a.size() && prefix < b.size() && a.get(prefix).equals(b.get(prefix))) {
            prefix++;
        }
        int suffix = 0;
        while (suffix < a.size() - prefix && suffix < b.size() - prefix
                && a.get(a.size() - 1 - suffix).equals(b.get(b.size() - 1 - suffix))) {
            suffix++;
        }
        List<Line> midA = a.subList(prefix, a.size() - suffix);
        List<Line> midB = b.subList(prefix, b.size() - suffix);
        List<Op> ops = new ArrayList<>();
        for (int k = 0; k < prefix; k++) {
            ops.add(new Op(' ', a.get(k)));
        }
        ops.addAll((long) midA.size() * midB.size() > MAX_CELLS
                ? whole(midA, midB)
                : script(midA, midB));
        for (int k = a.size() - suffix; k < a.size(); k++) {
            ops.add(new Op(' ', a.get(k)));
        }
        return ops;
    }

    /** Both texts in full, one replacing the other — the answer when finding what they share costs
     * more than {@link #MAX_CELLS}. */
    private static List<Op> whole(List<Line> a, List<Line> b) {
        List<Op> ops = new ArrayList<>();
        for (Line line : a) {
            ops.add(new Op('-', line));
        }
        for (Line line : b) {
            ops.add(new Op('+', line));
        }
        return ops;
    }

    private static List<Op> script(List<Line> a, List<Line> b) {
        int n = a.size();
        int m = b.size();
        int[][] common = new int[n + 1][m + 1];
        for (int i = n - 1; i >= 0; i--) {
            for (int j = m - 1; j >= 0; j--) {
                common[i][j] = a.get(i).equals(b.get(j))
                        ? common[i + 1][j + 1] + 1
                        : Math.max(common[i + 1][j], common[i][j + 1]);
            }
        }
        List<Op> ops = new ArrayList<>();
        int i = 0;
        int j = 0;
        while (i < n && j < m) {
            if (a.get(i).equals(b.get(j))) {
                ops.add(new Op(' ', a.get(i)));
                i++;
                j++;
            } else if (common[i + 1][j] >= common[i][j + 1]) {
                ops.add(new Op('-', a.get(i)));
                i++;
            } else {
                ops.add(new Op('+', b.get(j)));
                j++;
            }
        }
        while (i < n) {
            ops.add(new Op('-', a.get(i++)));
        }
        while (j < m) {
            ops.add(new Op('+', b.get(j++)));
        }
        return ops;
    }

    /** The changed lines with their context, one hunk per run of them. */
    private static void render(List<Op> ops, StringBuilder out) {
        int[] fromAt = new int[ops.size() + 1];
        int[] toAt = new int[ops.size() + 1];
        for (int k = 0; k < ops.size(); k++) {
            char kind = ops.get(k).kind();
            fromAt[k + 1] = fromAt[k] + (kind == '+' ? 0 : 1);
            toAt[k + 1] = toAt[k] + (kind == '-' ? 0 : 1);
        }
        int k = 0;
        while (k < ops.size()) {
            if (ops.get(k).kind() == ' ') {
                k++;
                continue;
            }
            int start = Math.max(0, k - CONTEXT);
            int last = k;
            // Runs closer than twice the context share one hunk: written apart they would repeat the
            // lines between them, once as the first hunk's trailing context and once as the second's
            // leading context.
            for (int scan = k; scan < ops.size(); scan++) {
                if (ops.get(scan).kind() != ' ') {
                    last = scan;
                } else if (scan - last > CONTEXT * 2) {
                    break;
                }
            }
            int end = Math.min(ops.size(), last + CONTEXT + 1);
            hunk(ops, start, end, fromAt, toAt, out);
            k = end;
        }
    }

    private static void hunk(List<Op> ops, int start, int end, int[] fromAt, int[] toAt,
            StringBuilder out) {
        int fromCount = fromAt[end] - fromAt[start];
        int toCount = toAt[end] - toAt[start];
        out.append("@@ -").append(at(fromAt[start], fromCount)).append(',').append(fromCount)
                .append(" +").append(at(toAt[start], toCount)).append(',').append(toCount)
                .append(" @@\n");
        for (int k = start; k < end; k++) {
            Op op = ops.get(k);
            out.append(op.kind()).append(op.line().text()).append('\n');
            if (!op.line().terminated()) {
                out.append("\\ No newline at end of file\n");
            }
        }
    }

    /** Where a hunk starts on one side: the first line it covers, or the line it follows when it
     * covers none of that side at all. */
    private static int at(int before, int count) {
        return count == 0 ? before : before + 1;
    }
}
