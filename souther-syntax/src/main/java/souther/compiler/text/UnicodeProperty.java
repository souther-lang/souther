package souther.compiler.text;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Set;

/**
 * A set of code points the language reads off the Unicode Character Database, against the version
 * the data names.
 *
 * <p>The language owns every character property it is defined by rather than asking the running
 * JDK. {@code Character.isLetter} and its kin answer against whatever Unicode version the JDK a
 * compile happens to run on carries, so a rule written with them moves when the JDK does, and a
 * body one compiler admitted another refuses. What is read here is the database's own text, an
 * excerpt of one of its property files carried as a resource: the lines of the values the language
 * needs, under the file's own header, whose first line names the version ({@code #
 * DerivedGeneralCategory-18.0.0.txt}). Moving to a later version is replacing that excerpt, which
 * is a change to what the language reads.
 *
 * <p>The format is the one the database's derived property files share: a code point or a range
 * {@code 0041..005A}, a semicolon, the value, and a comment.
 */
public final class UnicodeProperty {

    /** The first 128 code points, answered without a search: most text is ASCII. */
    private static final int ASCII = 128;

    private final String unicodeVersion;
    /** Sorted, non-overlapping {@code [from, to]} pairs, flattened. */
    private final int[] ranges;
    private final boolean[] ascii = new boolean[ASCII];

    private UnicodeProperty(String unicodeVersion, int[] ranges) {
        this.unicodeVersion = unicodeVersion;
        this.ranges = ranges;
        for (int codePoint = 0; codePoint < ASCII; codePoint++) {
            ascii[codePoint] = search(codePoint);
        }
    }

    /**
     * The code points the excerpt {@code resource}, beside {@code owner}, gives one of the values
     * {@code taken}.
     *
     * @param file    the property file it is an excerpt of, {@code DerivedCoreProperties}
     * @param written every value the excerpt holds; a line of any other is refused, so an excerpt
     *                holding more than it was cut to hold is found where it is read
     * @param taken   the values whose code points make this set
     */
    public static UnicodeProperty read(Class<?> owner, String resource, String file,
                                       Set<String> written, Set<String> taken) {
        if (!written.containsAll(taken)) {
            throw new IllegalArgumentException("a value is taken that the excerpt does not hold: "
                    + taken);
        }
        List<int[]> held = new ArrayList<>();
        String version = null;
        boolean first = true;
        try (InputStream in = owner.getResourceAsStream(resource)) {
            if (in == null) {
                throw new IllegalStateException("the Unicode data " + resource + " is missing");
            }
            BufferedReader reader = new BufferedReader(
                    new InputStreamReader(in, StandardCharsets.UTF_8));
            String line;
            while ((line = reader.readLine()) != null) {
                if (first) {
                    version = versionIn(line, file);
                    first = false;
                }
                int comment = line.indexOf('#');
                String stated = (comment < 0 ? line : line.substring(0, comment)).trim();
                if (stated.isEmpty()) {
                    continue;
                }
                int semicolon = stated.indexOf(';');
                if (semicolon < 0) {
                    throw new IllegalStateException("a property line with no value: " + line);
                }
                String value = stated.substring(semicolon + 1).trim();
                if (!written.contains(value)) {
                    throw new IllegalStateException(
                            resource + " holds a value it was not cut to hold: " + line);
                }
                if (taken.contains(value)) {
                    held.add(range(stated.substring(0, semicolon).trim()));
                }
            }
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
        if (version == null) {
            throw new IllegalStateException(resource + " names no Unicode version");
        }
        return new UnicodeProperty(version, packed(held, resource));
    }

    /** The Unicode version the set is read against, taken from the excerpt's own first line so
     *  that the data and the version it is called cannot come apart. */
    public String unicodeVersion() {
        return unicodeVersion;
    }

    /** Whether {@code codePoint} is in the set. */
    public boolean has(int codePoint) {
        return codePoint >= 0 && codePoint < ASCII ? ascii[codePoint] : search(codePoint);
    }

    /** The set as sorted, non-overlapping {@code [from, to]} pairs, flattened. */
    public int[] ranges() {
        return ranges.clone();
    }

    private static String versionIn(String line, String file) {
        String prefix = "# " + file + "-";
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
     * The ranges in order, flattened into one array.
     *
     * <p>A file lists a property value by value, so the ranges of several values come in several
     * runs; put in order they never overlap, since a code point has one value of a property. An
     * overlap is refused here, the one place it can be seen: the search answers only if it does not
     * hold, and everything downstream asks the search and would be told the same wrong answer.
     */
    private static int[] packed(List<int[]> ranges, String resource) {
        if (ranges.isEmpty()) {
            throw new IllegalStateException(resource + " holds no code point it was asked for");
        }
        List<int[]> sorted = new ArrayList<>(ranges);
        sorted.sort(Comparator.comparingInt(range -> range[0]));
        int[] out = new int[sorted.size() * 2];
        int previous = -1;
        for (int i = 0; i < sorted.size(); i++) {
            int[] range = sorted.get(i);
            if (range[0] <= previous) {
                throw new IllegalStateException(resource + " gives two values to "
                        + Integer.toHexString(range[0]));
            }
            previous = range[1];
            out[i * 2] = range[0];
            out[i * 2 + 1] = range[1];
        }
        return out;
    }

    private boolean search(int codePoint) {
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
