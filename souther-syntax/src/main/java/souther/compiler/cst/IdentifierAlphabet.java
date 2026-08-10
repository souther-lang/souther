package souther.compiler.cst;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;

/**
 * Which characters a name is made of. Souther's identifier is UAX #31's default form,
 * {@code XID_Start XID_Continue*}, against the Unicode version this file names.
 *
 * <p>The language owns this rather than borrowing it. Asking the running JDK — {@code
 * Character.isJavaIdentifierStart} — answers Java's question, which admits {@code $} and a leading
 * {@code _} because Java wanted them, and there is no version in the answer at all: the alphabet
 * would then move with whatever JDK a compile happens to run on, and a name is part of what a
 * compiled module promises, since a published helper's body travels in the jar as source and is
 * lexed again by the importing compiler.
 *
 * <p>The alphabet is the Unicode Character Database's own text, carried as a resource and read
 * here. It is not a table generated from that text, because a generated table is a second copy of
 * an answer and would have to be kept in step with the first; and it is not derived from general
 * categories either, because UAX #44 says to take {@code XID_Start} and {@code XID_Continue} from
 * {@code DerivedCoreProperties.txt} rather than to re-derive them. Moving to a later Unicode
 * version is replacing that one file, which is a change to what the language reads and moves the
 * boundary version with it.
 */
public final class IdentifierAlphabet {

    private IdentifierAlphabet() {}

    /** The property file, an excerpt of {@code DerivedCoreProperties.txt} holding its header and
     *  the two properties a name is spelled from. */
    private static final String RESOURCE = "identifier-alphabet.txt";

    private static final String VERSION;
    /** Start and continue, each as sorted, non-overlapping {@code [from, to]} pairs. */
    private static final int[] START;
    private static final int[] CONTINUE;
    /** The first 128 code points, answered without a search: source is mostly ASCII. */
    private static final boolean[] ASCII_START = new boolean[128];
    private static final boolean[] ASCII_CONTINUE = new boolean[128];

    static {
        List<int[]> start = new ArrayList<>();
        List<int[]> continues = new ArrayList<>();
        String version = null;
        try (InputStream in = IdentifierAlphabet.class.getResourceAsStream(RESOURCE)) {
            if (in == null) {
                throw new IllegalStateException("the identifier alphabet " + RESOURCE + " is missing");
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
                    throw new IllegalStateException("a property line with no property: " + line);
                }
                int[] range = range(stated.substring(0, semicolon).trim());
                switch (stated.substring(semicolon + 1).trim()) {
                    case "XID_Start" -> start.add(range);
                    case "XID_Continue" -> continues.add(range);
                    default -> throw new IllegalStateException(
                            "the alphabet holds a property it is not spelled from: " + line);
                }
            }
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
        if (version == null) {
            throw new IllegalStateException("the identifier alphabet names no Unicode version");
        }
        VERSION = version;
        START = packed(start, "XID_Start");
        CONTINUE = packed(continues, "XID_Continue");
        for (int codePoint = 0; codePoint < ASCII_START.length; codePoint++) {
            ASCII_START[codePoint] = holds(START, codePoint);
            ASCII_CONTINUE[codePoint] = holds(CONTINUE, codePoint);
        }
    }

    /** The Unicode version the alphabet is read against, taken from the file's own first line
     *  ({@code # DerivedCoreProperties-17.0.0.txt}) so that the data and the version it is called
     *  cannot come apart. */
    public static String unicodeVersion() {
        return VERSION;
    }

    /** Whether a name may begin with {@code codePoint}. */
    public static boolean isStart(int codePoint) {
        return codePoint < 128 ? codePoint >= 0 && ASCII_START[codePoint] : holds(START, codePoint);
    }

    /** Whether a name may carry on with {@code codePoint}. Every start is a continue, so this is
     *  the wider of the two. */
    public static boolean isContinue(int codePoint) {
        return codePoint < 128 ? codePoint >= 0 && ASCII_CONTINUE[codePoint]
                : holds(CONTINUE, codePoint);
    }

    /**
     * Whether {@code written} is a name.
     *
     * <p>A name in a source file is a name because the scan read it as one. A name arriving from
     * outside a source file was read by nothing — the stem of a file the compiler was pointed at,
     * the name an embedding gives a source with no header — and is held to the alphabet here
     * instead, so that what a module may be called does not depend on which way it was named.
     */
    public static boolean isName(String written) {
        if (written == null || written.isEmpty() || !isStart(written.codePointAt(0))) {
            return false;
        }
        return written.codePoints().skip(1).allMatch(IdentifierAlphabet::isContinue);
    }

    /**
     * The characters a name may begin with, written as the body of a regular expression's character
     * class ({@code A-Za-z\x{00AA}…}).
     *
     * <p>A tool that colours source cannot call the two questions above — an editor grammar is a
     * regular expression and runs in an engine of its own — so what it can be given is the same
     * answer in the form it does read. Written from the ranges here rather than approximated by an
     * ASCII pattern or a Unicode property the engine may not have, so the editor and the compiler
     * admit one set of names and a test can hold them against each other.
     */
    public static String startClass() {
        return characterClass(START);
    }

    /** The characters a name may carry on with, as a character class body. */
    public static String continueClass() {
        return characterClass(CONTINUE);
    }

    private static String characterClass(int[] ranges) {
        StringBuilder out = new StringBuilder();
        for (int i = 0; i < ranges.length; i += 2) {
            out.append(escaped(ranges[i]));
            if (ranges[i + 1] != ranges[i]) {
                out.append('-').append(escaped(ranges[i + 1]));
            }
        }
        return out.toString();
    }

    /** A code point as a class writes it: the letters and digits as themselves, so that the common
     *  part of the class stays readable, and everything else by number. */
    private static String escaped(int codePoint) {
        boolean plain = (codePoint >= 'a' && codePoint <= 'z')
                || (codePoint >= 'A' && codePoint <= 'Z')
                || (codePoint >= '0' && codePoint <= '9');
        return plain ? String.valueOf((char) codePoint) : String.format("\\x{%04X}", codePoint);
    }

    private static String versionIn(String line) {
        String prefix = "# DerivedCoreProperties-";
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
     * are flattened.
     *
     * <p>The file is sorted and its ranges do not touch, and the search below answers only if that
     * holds. Checking it where the data is read is the one place it can be checked at all: nothing
     * downstream would report an unsorted range, because everything downstream asks this and would
     * be told the same wrong answer.
     */
    private static int[] packed(List<int[]> ranges, String property) {
        int[] out = new int[ranges.size() * 2];
        int previous = -1;
        for (int i = 0; i < ranges.size(); i++) {
            int[] range = ranges.get(i);
            if (range[0] <= previous) {
                throw new IllegalStateException(
                        property + " is not in ascending order at " + Integer.toHexString(range[0]));
            }
            previous = range[1];
            out[i * 2] = range[0];
            out[i * 2 + 1] = range[1];
        }
        if (out.length == 0) {
            throw new IllegalStateException(property + " holds no code point");
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
