package souther.compiler.jvm;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;

/**
 * The simple uppercase mapping of the Unicode Character Database, against the version the data
 * names: one code point to one, field 12 of {@code UnicodeData.txt}.
 *
 * <p>What capitalizes a behavior's name into its class name (spec §jvm-behavior), which is part of
 * what a published class is called and what another module links against. Asked of the running JDK
 * — {@code Character.toUpperCase} — the answer would move with whatever Unicode version that JDK
 * carries, so one behavior would be two classes under two JDKs. The version is the one the language
 * fixes for case conversion.
 *
 * <p>The data is the database's own text: the lines of {@code UnicodeData.txt} that give a simple
 * uppercase mapping, under a first line naming the version.
 */
final class SimpleUppercase {

    private SimpleUppercase() {}

    private static final String RESOURCE = "simple-uppercase.txt";
    private static final String HEADER_PREFIX = "# UnicodeData-";
    private static final String HEADER_SUFFIX = ".txt";

    private static final String VERSION;
    /** The code points that have a mapping, ascending. */
    private static final int[] FROM;
    /** What each maps to, at the same index. */
    private static final int[] TO;

    static {
        List<int[]> pairs = new ArrayList<>();
        String version = null;
        boolean first = true;
        try (InputStream in = SimpleUppercase.class.getResourceAsStream(RESOURCE)) {
            if (in == null) {
                throw new IllegalStateException("the Unicode data " + RESOURCE + " is missing");
            }
            BufferedReader reader = new BufferedReader(
                    new InputStreamReader(in, StandardCharsets.UTF_8));
            String line;
            while ((line = reader.readLine()) != null) {
                if (first) {
                    if (line.startsWith(HEADER_PREFIX) && line.endsWith(HEADER_SUFFIX)) {
                        version = line.substring(HEADER_PREFIX.length(),
                                line.length() - HEADER_SUFFIX.length());
                    }
                    first = false;
                }
                if (line.isEmpty() || line.startsWith("#")) {
                    continue;
                }
                String[] fields = line.split(";", -1);
                if (fields.length != 15 || fields[12].isEmpty()) {
                    throw new IllegalStateException("not a line with an uppercase mapping: " + line);
                }
                pairs.add(new int[] {Integer.parseInt(fields[0], 16),
                        Integer.parseInt(fields[12], 16)});
            }
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
        if (version == null) {
            throw new IllegalStateException(RESOURCE + " names no Unicode version");
        }
        VERSION = version;
        FROM = new int[pairs.size()];
        TO = new int[pairs.size()];
        for (int i = 0; i < pairs.size(); i++) {
            FROM[i] = pairs.get(i)[0];
            TO[i] = pairs.get(i)[1];
            // The search below answers only over ascending code points, and this is the one place
            // an out-of-order line can be seen.
            if (i > 0 && FROM[i] <= FROM[i - 1]) {
                throw new IllegalStateException(RESOURCE + " is not in ascending order at "
                        + Integer.toHexString(FROM[i]));
            }
        }
    }

    /** The Unicode version the mapping is read against. */
    static String unicodeVersion() {
        return VERSION;
    }

    /** What {@code codePoint} maps to, or itself where it has no mapping. */
    static int of(int codePoint) {
        int low = 0;
        int high = FROM.length - 1;
        while (low <= high) {
            int middle = (low + high) >>> 1;
            if (FROM[middle] < codePoint) {
                low = middle + 1;
            } else if (FROM[middle] > codePoint) {
                high = middle - 1;
            } else {
                return TO[middle];
            }
        }
        return codePoint;
    }
}
