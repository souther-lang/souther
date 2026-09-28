import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

/**
 * Checks {@code souther.unicode.Normalization.nfc} against Unicode 18.0.0's
 * {@code NormalizationTest.txt} in full — the conformance oracle for
 * {@code NormalizationTables.java}/{@code Normalization.java}, run by hand rather than kept as a
 * Maven test for the reason {@code GenerateCaseTables.java}'s regeneration step already gives: a
 * multi-megabyte upstream corpus does not belong in this repository, and a Unicode version bump
 * is a deliberate, separate step, not something {@code mvn} discovers on its own.
 *
 * <p>Each data line is five semicolon-separated columns — source, NFC, NFD, NFKC, NFKD — of
 * space-separated hex code points, followed by a {@code #} comment this reads no further than.
 * Only the first two matter here: the file's own conformance clause for column 2 is
 * {@code c2 == toNFC(c1) == toNFC(c2) == toNFC(c3)} (a fourth check to run once NFD exists), so
 * every one of the three is checked against every data line, not only the source column.
 *
 * <p>Fails closed on the input's own version header, the same check
 * {@code GenerateNormalizationTables.java} runs on its three inputs: a {@code NormalizationTest.txt}
 * for a different Unicode version would silently check {@link souther.unicode.Normalization#nfc}
 * against the wrong oracle rather than the tables it was actually generated from.
 *
 * <pre>java bin/VerifyNormalization.java &lt;NormalizationTest.txt&gt;</pre>
 */
public final class VerifyNormalization {

    private static final String UNICODE_VERSION = "18.0.0";

    private VerifyNormalization() {}

    public static void main(String[] args) throws IOException {
        if (args.length != 1) {
            System.err.println("usage: java bin/VerifyNormalization.java <NormalizationTest.txt>");
            System.exit(1);
        }
        Path path = Path.of(args[0]);
        checkVersionHeader(path);
        List<String> lines = Files.readAllLines(path, StandardCharsets.UTF_8);
        int checked = 0;
        int failed = 0;
        for (int lineNo = 1; lineNo <= lines.size(); lineNo++) {
            String raw = lines.get(lineNo - 1);
            String data = raw.replaceFirst("#.*", "").trim();
            if (data.isEmpty() || data.startsWith("@")) {
                continue;
            }
            String[] columns = data.split(";", -1);
            if (columns.length < 3) {
                continue;
            }
            String c1 = decode(columns[0]);
            String c2 = decode(columns[1]);
            String c3 = decode(columns[2]);
            checked++;
            failed += checkNfc(lineNo, "c1", c1, c2) ? 0 : 1;
            failed += checkNfc(lineNo, "c2", c2, c2) ? 0 : 1;
            failed += checkNfc(lineNo, "c3", c3, c2) ? 0 : 1;
        }
        System.out.println(checked + " data lines, " + (checked * 3) + " NFC checks, " + failed + " failed");
        if (failed > 0) {
            System.exit(1);
        }
    }

    /** {@code # NormalizationTest-<version>.txt}, the same first-line check
     *  {@code GenerateNormalizationTables.java} runs on its own two versioned inputs. */
    private static void checkVersionHeader(Path path) throws IOException {
        String firstLine = Files.readAllLines(path, StandardCharsets.UTF_8).get(0);
        String expected = "# NormalizationTest-" + UNICODE_VERSION + ".txt";
        if (!firstLine.equals(expected)) {
            throw new IllegalStateException(
                    path + " does not open with " + expected + " (found: " + firstLine + ") — this"
                            + " verifier is pinned to Unicode " + UNICODE_VERSION + ", the same"
                            + " version NormalizationTables.java was generated from; a different"
                            + " version's corpus is not this table's oracle");
        }
    }

    private static boolean checkNfc(int lineNo, String column, String input, String expected) {
        String actual = souther.unicode.Normalization.nfc(input);
        if (actual.equals(expected)) {
            return true;
        }
        System.out.println("line " + lineNo + " (" + column + "): nfc(" + hex(input) + ") = " + hex(actual)
                + ", expected " + hex(expected));
        return false;
    }

    private static String decode(String hexList) {
        StringBuilder out = new StringBuilder();
        for (String token : hexList.trim().split("\\s+")) {
            out.appendCodePoint(Integer.parseInt(token, 16));
        }
        return out.toString();
    }

    private static String hex(String s) {
        StringBuilder sb = new StringBuilder();
        s.codePoints().forEach(cp -> sb.append(Integer.toHexString(cp)).append(' '));
        return sb.toString().trim();
    }
}
