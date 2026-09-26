import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

/**
 * Regenerates {@code souther-runtime/.../souther/unicode/NormalizationTables.java} from the
 * Unicode Character Database (spec §stdlib-string).
 *
 * <p>Reads {@code UnicodeData.txt} and {@code CompositionExclusions.txt} for one pinned Unicode
 * version and emits three tables: the one-step canonical decomposition mapping (a compatibility
 * decomposition — one with a {@code <tag>} — is not this), the non-zero canonical combining
 * classes, and the composition exclusions {@code CompositionExclusions.txt} states outright (the
 * ones "script specific" enough that nothing in {@code UnicodeData.txt} implies them).
 *
 * <p>Composition is not a fourth table. Two of the three ways a code point is excluded from
 * composing — its canonical decomposition has one member (a singleton), or the first member is
 * not a starter (non-zero combining class) — are exactly what {@code Normalization.compose} reads off
 * {@code DECOMP} and {@code CCC} already; storing a derived composition table beside the
 * decomposition table it was derived from would let a hand slip and the two disagree. Composing
 * from decomposition, at the one place that reads both, is what keeps that impossible.
 *
 * <p>Reads {@code DerivedNormalizationProps.txt} only to check this generator's own derivation —
 * script-specific exclusions plus singleton and non-starter decompositions, recomputed here —
 * against the {@code Full_Composition_Exclusion} property Unicode publishes for the same version.
 * It is an oracle for this file's correctness, not a fourth runtime input; nothing it says reaches
 * {@code NormalizationTables.java}.
 *
 * <p>Fails closed: a version header that does not read Unicode {@link #UNICODE_VERSION}, or a
 * derived exclusion set that does not exactly match {@code Full_Composition_Exclusion}, stops the
 * run rather than emitting a plausible-looking wrong table.
 *
 * <p>Not part of the Maven build, for the reason {@code GenerateCaseTables.java} gives: a Unicode
 * version bump is a specification change, not a dependency bump. Run from the repository root:
 *
 * <pre>java bin/GenerateNormalizationTables.java &lt;ucd-directory&gt;</pre>
 *
 * <p>where {@code <ucd-directory>} holds the three files above plus {@code NormalizationTest.txt},
 * downloaded from {@code https://www.unicode.org/Public/<version>/ucd/} — the fourth file is not
 * read here; {@code bin/VerifyNormalization.java} runs it against the generated tables afterward.
 */
public final class GenerateNormalizationTables {

    private static final Path OUTPUT =
            Path.of("souther-runtime/src/main/java/souther/unicode/NormalizationTables.java");
    private static final String UNICODE_VERSION = "18.0.0";

    private GenerateNormalizationTables() {}

    public static void main(String[] args) throws IOException, NoSuchAlgorithmException {
        if (args.length != 1) {
            System.err.println("usage: java bin/GenerateNormalizationTables.java <ucd-directory>");
            System.exit(1);
        }
        Path ucd = Path.of(args[0]);
        Path unicodeData = ucd.resolve("UnicodeData.txt");
        Path compositionExclusions = ucd.resolve("CompositionExclusions.txt");
        Path derivedNormalizationProps = ucd.resolve("DerivedNormalizationProps.txt");

        checkVersionHeader(compositionExclusions, "CompositionExclusions");
        checkVersionHeader(derivedNormalizationProps, "DerivedNormalizationProps");

        Map<Integer, Integer> ccc = new TreeMap<>();
        Map<Integer, int[]> decomp = new TreeMap<>();
        parseUnicodeData(unicodeData, ccc, decomp);

        Set<Integer> scriptSpecific = parseCompositionExclusions(compositionExclusions);
        Set<Integer> derivedFull = deriveFullExclusion(decomp, ccc, scriptSpecific);
        Set<Integer> published = parseFullCompositionExclusion(derivedNormalizationProps);
        if (!derivedFull.equals(published)) {
            Set<Integer> missing = new TreeSet<>(published);
            missing.removeAll(derivedFull);
            Set<Integer> extra = new TreeSet<>(derivedFull);
            extra.removeAll(published);
            throw new IllegalStateException(
                    "derived Full_Composition_Exclusion disagrees with " + derivedNormalizationProps
                            + " — missing " + hexSet(missing) + ", extra " + hexSet(extra)
                            + " — this generator's singleton/non-starter derivation is wrong, not the"
                            + " published property");
        }

        String source = render(decomp, ccc, scriptSpecific,
                checksum(unicodeData), checksum(compositionExclusions), checksum(derivedNormalizationProps));
        Files.writeString(OUTPUT, source, StandardCharsets.UTF_8);
        System.out.println("wrote " + OUTPUT + " (" + decomp.size() + " decompositions, " + ccc.size()
                + " non-zero combining classes, " + scriptSpecific.size() + " script-specific exclusions,"
                + " verified against " + published.size() + " published Full_Composition_Exclusion entries)");
    }

    /** Neither file states its own version in {@code UnicodeData.txt}'s bare-line format, but both
     *  files this generator reads besides it are a {@code # <FileName>-<version>.txt} first line. */
    private static void checkVersionHeader(Path path, String fileName) throws IOException {
        String firstLine = Files.readAllLines(path, StandardCharsets.UTF_8).get(0);
        String expected = "# " + fileName + "-" + UNICODE_VERSION + ".txt";
        if (!firstLine.equals(expected)) {
            throw new IllegalStateException(
                    path + " does not open with " + expected + " (found: " + firstLine + ") — this"
                            + " generator is pinned to Unicode " + UNICODE_VERSION + "; update"
                            + " UNICODE_VERSION and re-verify every witness before regenerating"
                            + " against a different one");
        }
    }

    /** {@code UnicodeData.txt} fields, 0-indexed: 3 is the canonical combining class, 5 is the
     *  decomposition mapping — present and NOT starting with {@code <} is a canonical decomposition;
     *  present and starting with {@code <tag>} is compatibility-only and not this table's business. */
    private static void parseUnicodeData(Path path, Map<Integer, Integer> ccc, Map<Integer, int[]> decomp)
            throws IOException {
        for (String line : Files.readAllLines(path, StandardCharsets.UTF_8)) {
            if (line.isBlank()) {
                continue;
            }
            String[] f = line.split(";", -1);
            int cp = Integer.parseInt(f[0], 16);
            int cccValue = Integer.parseInt(f[3]);
            if (cccValue != 0) {
                ccc.put(cp, cccValue);
            }
            String decomposition = f[5].trim();
            if (!decomposition.isEmpty() && decomposition.charAt(0) != '<') {
                decomp.put(cp, codePoints(decomposition));
            }
        }
    }

    private static int[] codePoints(String hexList) {
        String[] parts = hexList.split("\\s+");
        int[] result = new int[parts.length];
        for (int i = 0; i < parts.length; i++) {
            result[i] = Integer.parseInt(parts[i], 16);
        }
        return result;
    }

    /** The bare hex-code-point lines before the first blank/comment-only section this file's
     *  header explains as "cannot be derived from {@code UnicodeData.txt}" — every other line is
     *  a comment, including the four non-starter examples quoted for reference near the end,
     *  which a bare {@code #} prefix already excludes. */
    private static Set<Integer> parseCompositionExclusions(Path path) throws IOException {
        Set<Integer> exclusions = new TreeSet<>();
        for (String rawLine : Files.readAllLines(path, StandardCharsets.UTF_8)) {
            String line = rawLine.replaceFirst("#.*", "").trim();
            if (line.isEmpty()) {
                continue;
            }
            exclusions.add(Integer.parseInt(line, 16));
        }
        return exclusions;
    }

    /** {@code Full_Composition_Exclusion} = script-specific exclusions, plus every code point
     *  whose canonical decomposition is a singleton, plus every code point whose canonical
     *  decomposition's first member is not a starter (spec: {@code CompositionExclusions.txt}'s
     *  own header, "Generated from: Composition Exclusions + Singletons + Non-Starter
     *  Decompositions"). Recomputing the last two here rather than reading them off
     *  {@code DerivedNormalizationProps.txt} is the point: {@code Normalization.compose} derives
     *  composition eligibility from {@code DECOMP}/{@code CCC} the same way at run time, so the
     *  two cannot disagree — this method is what proves the derivation rule itself is right,
     *  against Unicode's own published answer. */
    private static Set<Integer> deriveFullExclusion(
            Map<Integer, int[]> decomp, Map<Integer, Integer> ccc, Set<Integer> scriptSpecific) {
        Set<Integer> full = new TreeSet<>(scriptSpecific);
        for (Map.Entry<Integer, int[]> e : decomp.entrySet()) {
            int[] mapped = e.getValue();
            if (mapped.length == 1 || ccc.getOrDefault(mapped[0], 0) != 0) {
                full.add(e.getKey());
            }
        }
        return full;
    }

    /** {@code <range-or-code-point> ; Full_Composition_Exclusion # <comment>}, expanded to every
     *  code point in range. This file states many derived properties; every line for a different
     *  one is skipped. */
    private static Set<Integer> parseFullCompositionExclusion(Path path) throws IOException {
        Set<Integer> published = new TreeSet<>();
        for (String rawLine : Files.readAllLines(path, StandardCharsets.UTF_8)) {
            String line = rawLine.replaceFirst("#.*", "").trim();
            if (line.isEmpty()) {
                continue;
            }
            String[] f = line.split(";", -1);
            if (f.length < 2 || !f[1].trim().equals("Full_Composition_Exclusion")) {
                continue;
            }
            String range = f[0].trim();
            int dots = range.indexOf("..");
            if (dots >= 0) {
                int start = Integer.parseInt(range.substring(0, dots), 16);
                int end = Integer.parseInt(range.substring(dots + 2), 16);
                for (int cp = start; cp <= end; cp++) {
                    published.add(cp);
                }
            } else {
                published.add(Integer.parseInt(range, 16));
            }
        }
        return published;
    }

    private static String hexSet(Set<Integer> cps) {
        StringBuilder sb = new StringBuilder("[");
        for (Integer cp : cps) {
            if (sb.length() > 1) {
                sb.append(' ');
            }
            sb.append(hex(cp));
        }
        return sb.append(']').toString();
    }

    private static String checksum(Path path) throws IOException, NoSuchAlgorithmException {
        MessageDigest digest = MessageDigest.getInstance("SHA-256");
        byte[] hash = digest.digest(Files.readAllBytes(path));
        StringBuilder hex = new StringBuilder();
        for (byte b : hash) {
            hex.append(String.format("%02x", b));
        }
        return hex.toString();
    }

    private static String render(Map<Integer, int[]> decomp, Map<Integer, Integer> ccc,
            Set<Integer> scriptSpecificExclusions, String unicodeDataSha256,
            String compositionExclusionsSha256, String derivedNormalizationPropsSha256) {
        StringBuilder out = new StringBuilder();
        out.append("package souther.unicode;\n\n");
        out.append("/**\n");
        out.append(" * The Unicode ").append(UNICODE_VERSION)
                .append(" canonical decomposition, combining class and script-specific composition\n");
        out.append(" * exclusion data {@link Normalization#nfc} reads.\n");
        out.append(" *\n");
        out.append(" * <p>Generated from Unicode ").append(UNICODE_VERSION).append("'s {@code UnicodeData.txt}")
                .append(" and {@code CompositionExclusions.txt}\n")
                .append(" * ({@code https://www.unicode.org/Public/").append(UNICODE_VERSION).append("/ucd/})")
                .append(" by {@code bin/GenerateNormalizationTables.java},\n")
                .append(" * checked against {@code DerivedNormalizationProps.txt}'s")
                .append(" {@code Full_Composition_Exclusion} at generation time.\n");
        out.append(" * DO NOT EDIT — regenerate on a Unicode version bump with")
                .append(" {@code java bin/GenerateNormalizationTables.java <ucd-directory>},\n");
        out.append(" * which this file's source checksums let a reviewer confirm ran against the version it claims.\n");
        out.append(" *\n");
        out.append(" * <p>SHA-256, of the three input files as downloaded:\n");
        out.append(" * <ul>\n");
        out.append(" * <li>UnicodeData.txt: {@code ").append(unicodeDataSha256).append("}\n");
        out.append(" * <li>CompositionExclusions.txt: {@code ").append(compositionExclusionsSha256).append("}\n");
        out.append(" * <li>DerivedNormalizationProps.txt: {@code ")
                .append(derivedNormalizationPropsSha256).append("}\n");
        out.append(" * </ul>\n");
        out.append(" */\n");
        out.append("final class NormalizationTables {\n\n");
        out.append("    private NormalizationTables() {}\n\n");
        out.append(DECODER_SOURCE);

        out.append("    /** Unicode ").append(UNICODE_VERSION).append("'s one-step canonical decomposition")
                .append(" mapping (").append(decomp.size())
                .append(" code points); every other code point has none. A compatibility ({@code <tag>})")
                .append(" decomposition is a different question and is not here. */\n");
        out.append("    static final Mapping DECOMP = decodeMapping(\"").append(encodeMapping(decomp)).append("\");\n\n");

        out.append("    /** Unicode ").append(UNICODE_VERSION).append("'s non-zero canonical combining classes (")
                .append(ccc.size()).append(" code points); every other code point's is 0 — a starter. */\n");
        out.append("    static final int[] CCC_KEYS = decodeIntKeys(\"").append(encodeCccKeys(ccc)).append("\");\n");
        out.append("    static final int[] CCC_VALUES = decodeIntValues(\"").append(encodeCccValues(ccc)).append("\");\n\n");

        out.append("    /** {@code CompositionExclusions.txt}'s script-specific exclusions (")
                .append(scriptSpecificExclusions.size()).append(" code points) — the composition")
                .append(" eligibility {@code UnicodeData.txt} alone does not decide.")
                .append(" {@link Normalization#compose} folds the other two")
                .append(" {@code Full_Composition_Exclusion} categories (singleton and non-starter")
                .append(" decompositions) in from {@link #DECOMP}/{@link #CCC_KEYS} directly. */\n");
        out.append("    static final int[] SCRIPT_SPECIFIC_EXCLUSIONS = decodeSortedInts(\"")
                .append(encodeSortedInts(scriptSpecificExclusions)).append("\");\n");

        out.append("}\n");
        return out.toString();
    }

    /** Kept as ordinary, reviewed Java rather than generated, for the reason
     *  {@code GenerateCaseTables.java}'s decoder is: a literal large enough to hold this data does
     *  not fit the JVM's 64&nbsp;KB per-method bytecode limit as an array initializer, so the data
     *  is a compact string constant, decoded once at class load. */
    private static final String DECODER_SOURCE = """
                /** A code point and the code point(s) its canonical decomposition maps to. */
                record Mapping(int[] codePoints, int[][] mapped) {}

                /** Decodes a "{@code <cp>:<mapped>[+<mapped>...] ...}" string — hex code points, space
                 *  separated entries, {@code +} joining a multi-code-point mapping — sorted by
                 *  {@code <cp>} so a lookup can binary search it. */
                private static Mapping decodeMapping(String data) {
                    String[] tokens = data.isEmpty() ? new String[0] : data.split(" ");
                    int[] codePoints = new int[tokens.length];
                    int[][] mapped = new int[tokens.length][];
                    for (int i = 0; i < tokens.length; i++) {
                        int colon = tokens[i].indexOf(':');
                        codePoints[i] = Integer.parseInt(tokens[i].substring(0, colon), 16);
                        String[] parts = tokens[i].substring(colon + 1).split("\\\\+");
                        int[] m = new int[parts.length];
                        for (int j = 0; j < parts.length; j++) {
                            m[j] = Integer.parseInt(parts[j], 16);
                        }
                        mapped[i] = m;
                    }
                    return new Mapping(codePoints, mapped);
                }

                /** Decodes a space-separated hex-code-point list, sorted, into the keys half of a
                 *  parallel-array lookup. */
                private static int[] decodeIntKeys(String data) {
                    return decodeSortedInts(data);
                }

                /** Decodes a space-separated hex-value list, in the same order as the keys it is
                 *  paired with — not sorted itself, since the sort is by key. */
                private static int[] decodeIntValues(String data) {
                    String[] tokens = data.isEmpty() ? new String[0] : data.split(" ");
                    int[] values = new int[tokens.length];
                    for (int i = 0; i < tokens.length; i++) {
                        values[i] = Integer.parseInt(tokens[i], 16);
                    }
                    return values;
                }

                /** Decodes a space-separated, ascending hex-code-point list into a sorted array a
                 *  lookup can binary search. */
                private static int[] decodeSortedInts(String data) {
                    return decodeIntValues(data);
                }

            """.stripIndent();

    private static String encodeMapping(Map<Integer, int[]> mapping) {
        StringBuilder sb = new StringBuilder();
        for (Map.Entry<Integer, int[]> e : mapping.entrySet()) {
            if (!sb.isEmpty()) {
                sb.append(' ');
            }
            sb.append(hex(e.getKey())).append(':').append(joinHex(e.getValue(), "+"));
        }
        return sb.toString();
    }

    private static String encodeCccKeys(Map<Integer, Integer> ccc) {
        StringBuilder sb = new StringBuilder();
        for (Integer cp : ccc.keySet()) {
            if (!sb.isEmpty()) {
                sb.append(' ');
            }
            sb.append(hex(cp));
        }
        return sb.toString();
    }

    private static String encodeCccValues(Map<Integer, Integer> ccc) {
        StringBuilder sb = new StringBuilder();
        for (Integer value : ccc.values()) {
            if (!sb.isEmpty()) {
                sb.append(' ');
            }
            sb.append(hex(value));
        }
        return sb.toString();
    }

    private static String encodeSortedInts(Set<Integer> cps) {
        StringBuilder sb = new StringBuilder();
        for (Integer cp : cps) {
            if (!sb.isEmpty()) {
                sb.append(' ');
            }
            sb.append(hex(cp));
        }
        return sb.toString();
    }

    private static String hex(int v) {
        return Integer.toHexString(v).toUpperCase(java.util.Locale.ROOT);
    }

    private static String joinHex(int[] values, String sep) {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < values.length; i++) {
            if (i > 0) {
                sb.append(sep);
            }
            sb.append(hex(values[i]));
        }
        return sb.toString();
    }
}
