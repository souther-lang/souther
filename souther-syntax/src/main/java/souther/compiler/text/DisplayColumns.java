package souther.compiler.text;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;

/**
 * How many columns a text occupies when it is written out.
 *
 * <p>Souther has two ways of saying where something is and they are not the same number. A source
 * position — what {@code SourcePos} carries, what the LSP exchanges, what a JSON diagnostic
 * publishes — is an index into the text, counted in UTF-16 code units. A display position is what a
 * caret has to line up with, what a header bar is padded to, and what the formatter's width is
 * measured against. A full-width character is one code unit and two columns, so anything that
 * spends the first number as the second is wrong by the number of full-width characters before it.
 * This is the second number, and it is the only place it is worked out.
 *
 * <p>The convention is Souther's own and is deliberately not a reconstruction of what any one
 * terminal does. East Asian Width {@code W} and {@code F} are two columns; every other value —
 * including {@code Ambiguous}, which terminals genuinely disagree about — is one; a tab advances to
 * the next multiple of {@link #TAB_STOP}. It has to be a convention rather than an observation
 * because the formatter's canonical form is decided by it: a width read from the terminal the tool
 * happens to be run in would make the same file format differently in two windows.
 *
 * <p>Every code point gets an answer and the answers add up, which is the whole of the model. What
 * is left out is not a set of characters but a behaviour: nothing here composes. A combining mark
 * is measured on its own — {@code 3099} is in the table as wide and is answered two, rather than
 * folding into the letter before it — and a variation selector and an emoji sequence are read the
 * same way, as their parts. Anything that would have to look at more than one code point at a time
 * to answer is not modelled, and when it is, it is modelled here.
 *
 * <p>The widths are the Unicode Character Database's own text, carried as a resource and read here,
 * for the reasons {@code IdentifierAlphabet} carries its alphabet the same way. The two files move
 * independently, though: the alphabet says what a name is and so travels in a compiled module,
 * while a width decides only how something is laid out and printed and is carried in nothing.
 */
public final class DisplayColumns {

    private DisplayColumns() {}

    /** A tab advances to the next column that is a multiple of this. Eight is what terminals,
     *  pagers and text tooling use where nothing says otherwise. */
    public static final int TAB_STOP = 8;

    /** The property file, an excerpt of {@code EastAsianWidth.txt} holding its header and the two
     *  values that are wide. The values that are one column are not carried: they are everything
     *  the file does not name. */
    private static final String RESOURCE = "east-asian-width.txt";

    private static final String VERSION;
    /** The wide code points, as sorted, non-overlapping {@code [from, to]} pairs. */
    private static final int[] WIDE;

    static {
        List<int[]> wide = new ArrayList<>();
        String version = null;
        try (InputStream in = DisplayColumns.class.getResourceAsStream(RESOURCE)) {
            if (in == null) {
                throw new IllegalStateException("the width table " + RESOURCE + " is missing");
            }
            BufferedReader reader = new BufferedReader(
                    new InputStreamReader(in, StandardCharsets.UTF_8));
            String line;
            while ((line = reader.readLine()) != null) {
                if (version == null) {
                    version = versionIn(line);
                }
                int comment = line.indexOf('#');
                String stated = (comment < 0 ? line : line.substring(0, comment)).trim();
                if (stated.isEmpty()) {
                    continue;
                }
                int semicolon = stated.indexOf(';');
                if (semicolon < 0) {
                    throw new IllegalStateException("a width line with no value: " + line);
                }
                int[] range = range(stated.substring(0, semicolon).trim());
                switch (stated.substring(semicolon + 1).trim()) {
                    case "W", "F" -> wide.add(range);
                    default -> throw new IllegalStateException(
                            "the width table holds a value that is not wide: " + line);
                }
            }
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
        if (version == null) {
            throw new IllegalStateException("the width table names no Unicode version");
        }
        VERSION = version;
        WIDE = packed(wide);
    }

    /** The Unicode version the widths are read against, taken from the file's own first line
     *  ({@code # EastAsianWidth-17.0.0.txt}) so that the data and the version it is called cannot
     *  come apart. */
    public static String unicodeVersion() {
        return VERSION;
    }

    /**
     * The column {@code text} ends at, having begun at {@code column}.
     *
     * <p>This is the primitive rather than a width, because a tab has no width of its own: what it
     * advances by is decided by where it starts. A caller that has a starting column must pass it,
     * and one that is measuring a text with no place yet — a header, a table cell — asks
     * {@link #width}.
     *
     * <p>{@code text} is one line's worth. A line break is not a number of columns and is the
     * caller's to handle, since only the caller knows what the next line is indented to.
     */
    public static int advance(String text, int column) {
        int at = column;
        for (int i = 0; i < text.length(); ) {
            int codePoint = text.codePointAt(i);
            i += Character.charCount(codePoint);
            if (codePoint == '\t') {
                at += TAB_STOP - at % TAB_STOP;
            } else {
                at += isWide(codePoint) ? 2 : 1;
            }
        }
        return at;
    }

    /** How many columns {@code text} occupies written from the start of a line. A tab in it is
     *  measured from there, which is what makes this a special case of {@link #advance} rather
     *  than a second answer. */
    public static int width(String text) {
        return advance(text, 0);
    }

    /** {@code text} followed by enough spaces to reach {@code columns}, or {@code text} alone where
     *  it already fills them. What a fixed-width column in printed output needs, and what a format
     *  string's own field width cannot give: that width is applied inside the formatter, after the
     *  argument is in its hands, and counts UTF-16 code units. */
    public static String padRight(String text, int columns) {
        int written = width(text);
        return written >= columns ? text : text + " ".repeat(columns - written);
    }

    /** Whether {@code codePoint} is written two columns wide. */
    public static boolean isWide(int codePoint) {
        return codePoint >= 0x1100 && holds(WIDE, codePoint);
    }

    private static String versionIn(String line) {
        String prefix = "# EastAsianWidth-";
        String suffix = ".txt";
        if (!line.startsWith(prefix) || !line.endsWith(suffix)) {
            return null;
        }
        return line.substring(prefix.length(), line.length() - suffix.length());
    }

    /** {@code 0041} or {@code 0041..005A}, as {@code [from, to]}. */
    private static int[] range(String written) {
        int dots = written.indexOf("..");
        int from = Integer.parseInt(dots < 0 ? written : written.substring(0, dots), 16);
        int to = dots < 0 ? from : Integer.parseInt(written.substring(dots + 2), 16);
        if (to < from) {
            throw new IllegalStateException("a range that ends before it begins: " + written);
        }
        return new int[] {from, to};
    }

    /**
     * The ranges flattened into one array, and the order the search relies on checked while they
     * are flattened. Checking it where the data is read is the one place it can be checked at all:
     * nothing downstream would report an unsorted range, because everything downstream asks this
     * and would be told the same wrong answer.
     */
    private static int[] packed(List<int[]> ranges) {
        int[] out = new int[ranges.size() * 2];
        int previous = -1;
        for (int i = 0; i < ranges.size(); i++) {
            int[] range = ranges.get(i);
            if (range[0] <= previous) {
                throw new IllegalStateException(
                        "the width table is not in ascending order at "
                                + Integer.toHexString(range[0]));
            }
            previous = range[1];
            out[i * 2] = range[0];
            out[i * 2 + 1] = range[1];
        }
        if (out.length == 0) {
            throw new IllegalStateException("the width table holds no code point");
        }
        return out;
    }

    private static boolean holds(int[] ranges, int codePoint) {
        int low = 0;
        int high = ranges.length / 2 - 1;
        while (low <= high) {
            int middle = (low + high) >>> 1;
            if (codePoint < ranges[middle * 2]) {
                high = middle - 1;
            } else if (codePoint > ranges[middle * 2 + 1]) {
                low = middle + 1;
            } else {
                return true;
            }
        }
        return false;
    }
}
