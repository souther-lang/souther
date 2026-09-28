import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

/**
 * Regenerates {@code souther-runtime/.../souther/runtime/CaseTables.java} from the Unicode
 * Character Database (spec §stdlib-string, ADR-0119).
 *
 * <p>Reads {@code UnicodeData.txt}, {@code SpecialCasing.txt} and {@code DerivedCoreProperties.txt}
 * for one pinned Unicode version and emits the data ADR-0119's default case conversion reads:
 * the full lowercase/uppercase mapping, the one context-dependent ({@code Final_Sigma}) mapping,
 * and the {@code Cased}/{@code Case_Ignorable} ranges that condition it. Every locale-tailored
 * {@code SpecialCasing.txt} entry (a condition carrying a language ID such as {@code tr}, {@code az}
 * or {@code lt}) is read and discarded — ADR-0119's contract is untailored, so tailoring never
 * reaches the generated table.
 *
 * <p>Fails closed rather than generating a plausible-looking wrong table: a
 * {@code SpecialCasing.txt} condition outside the ones named above ({@link #KNOWN_TAILORING_LANGUAGES}
 * plus {@code Final_Sigma}) stops the run, and so does a {@code SpecialCasing.txt} or
 * {@code DerivedCoreProperties.txt} whose own version header does not match {@link #UNICODE_VERSION}.
 * Neither check assumes a mapping's width; {@code Final_Sigma} is read at whatever arity it comes at.
 *
 * <p>Not part of the Maven build: a Unicode version bump is a specification change, not a dependency
 * bump, so regenerating is a deliberate, separate step. Run from the repository root:
 *
 * <pre>java bin/GenerateCaseTables.java &lt;ucd-directory&gt;</pre>
 *
 * <p>where {@code <ucd-directory>} holds the three files above, downloaded from
 * {@code https://www.unicode.org/Public/<version>/ucd/}.
 */
public final class GenerateCaseTables {

    private static final Path OUTPUT =
            Path.of("souther-runtime/src/main/java/souther/runtime/CaseTables.java");
    private static final String UNICODE_VERSION = "18.0.0";

    private GenerateCaseTables() {}

    public static void main(String[] args) throws IOException, NoSuchAlgorithmException {
        if (args.length != 1) {
            System.err.println("usage: java bin/GenerateCaseTables.java <ucd-directory>");
            System.exit(1);
        }
        Path ucd = Path.of(args[0]);
        Path unicodeData = ucd.resolve("UnicodeData.txt");
        Path specialCasing = ucd.resolve("SpecialCasing.txt");
        Path derivedCoreProperties = ucd.resolve("DerivedCoreProperties.txt");

        Map<Integer, Integer> simpleLower = new TreeMap<>();
        Map<Integer, Integer> simpleUpper = new TreeMap<>();
        parseUnicodeData(unicodeData, simpleLower, simpleUpper);

        checkVersionHeader(specialCasing, "SpecialCasing");
        checkVersionHeader(derivedCoreProperties, "DerivedCoreProperties");

        Map<Integer, int[]> fullLower = new TreeMap<>();
        Map<Integer, int[]> fullUpper = new TreeMap<>();
        Map<Integer, int[]> finalSigmaLower = new TreeMap<>();
        parseSpecialCasing(specialCasing, fullLower, fullUpper, finalSigmaLower);

        List<int[]> cased = new ArrayList<>();
        List<int[]> caseIgnorable = new ArrayList<>();
        parseDerivedCoreProperties(derivedCoreProperties, cased, caseIgnorable);

        Map<Integer, int[]> lower = mergeMappings(simpleLower, fullLower);
        Map<Integer, int[]> upper = mergeMappings(simpleUpper, fullUpper);

        String source = render(lower, upper, finalSigmaLower, cased, caseIgnorable,
                checksum(unicodeData), checksum(specialCasing), checksum(derivedCoreProperties));
        Files.writeString(OUTPUT, source, StandardCharsets.UTF_8);
        System.out.println("wrote " + OUTPUT + " (" + lower.size() + " lowercase, " + upper.size()
                + " uppercase, " + finalSigmaLower.size() + " Final_Sigma entries, " + cased.size()
                + " Cased ranges, " + caseIgnorable.size() + " Case_Ignorable ranges)");
    }

    /** {@code UnicodeData.txt} carries no version header of its own — {@code SpecialCasing.txt} and
     *  {@code DerivedCoreProperties.txt} do, each a {@code # <FileName>-<version>.txt} first line —
     *  so those two are checked against {@link #UNICODE_VERSION} directly, catching the input
     *  directory not being the version this generator claims to have read from it. A checksum alone
     *  cannot: it proves the bytes match what was hashed, not that they are the version labelled. */
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

    /** {@code UnicodeData.txt} fields, 0-indexed: 12 is the simple uppercase mapping, 13 the simple
     *  lowercase mapping — one-to-one and independent of context and language, which is why
     *  {@code SpecialCasing.txt} calls out everything wider than that on its own. */
    private static void parseUnicodeData(Path path, Map<Integer, Integer> lower, Map<Integer, Integer> upper)
            throws IOException {
        for (String line : Files.readAllLines(path, StandardCharsets.UTF_8)) {
            if (line.isBlank()) {
                continue;
            }
            String[] f = line.split(";", -1);
            int cp = Integer.parseInt(f[0], 16);
            if (!f[12].isBlank()) {
                upper.put(cp, Integer.parseInt(f[12].trim(), 16));
            }
            if (!f[13].isBlank()) {
                lower.put(cp, Integer.parseInt(f[13].trim(), 16));
            }
        }
    }

    /** Condition lists this generator has checked are locale tailoring — read and discarded, since
     *  ADR-0119's contract carries none — rather than merely unrecognized. {@code SpecialCasing.txt}
     *  documents the condition list as "language IDs or casing contexts" and warns a parser to
     *  expect more of either kind in a later version; a language ID may gain a fourth member, but a
     *  new language-insensitive *context* (the {@code Final_Sigma} kind) is exactly the case that
     *  must not fall into this set by default. */
    private static final Set<String> KNOWN_TAILORING_LANGUAGES = Set.of("lt", "tr", "az");

    /** {@code <code>; <lower>; <title>; <upper>; (<condition_list>;)?} per file. A blank condition
     *  list is the unconditional full mapping ADR-0119 uses; {@code Final_Sigma} is the one
     *  condition Unicode 18.0.0 states that is context, not locale, and so is kept, at whatever
     *  arity it maps to — not assumed to be one code point. Every condition in
     *  {@link #KNOWN_TAILORING_LANGUAGES} is a checked, deliberate exclusion. Anything else fails
     *  the generation rather than being silently treated as more of the same: a condition list this
     *  generator has not been told about is exactly the shape a Unicode version bump could add
     *  (the file format's own words are "language IDs or casing contexts", and it says to expect
     *  more of either), and ADR-0119 requires that to be caught here, not modeled wrong. */
    private static void parseSpecialCasing(Path path, Map<Integer, int[]> lower, Map<Integer, int[]> upper,
            Map<Integer, int[]> finalSigmaLower) throws IOException {
        for (String rawLine : Files.readAllLines(path, StandardCharsets.UTF_8)) {
            String line = rawLine.replaceFirst("#.*", "");
            if (line.isBlank()) {
                continue;
            }
            String[] f = line.split(";", -1);
            int cp = Integer.parseInt(f[0].trim(), 16);
            String condition = f.length > 4 ? f[4].trim() : "";
            if (condition.isEmpty()) {
                lower.put(cp, codePoints(f[1]));
                upper.put(cp, codePoints(f[3]));
            } else if (condition.equalsIgnoreCase("Final_Sigma")) {
                finalSigmaLower.put(cp, codePoints(f[1]));
            } else if (KNOWN_TAILORING_LANGUAGES.contains(firstWord(condition).toLowerCase(java.util.Locale.ROOT))) {
                // deliberately discarded: locale tailoring, outside ADR-0119's untailored contract.
            } else {
                throw new IllegalStateException(
                        "unrecognized SpecialCasing.txt condition \"" + condition + "\" at U+"
                                + hex(cp) + " — is this a new untailored context Unicode "
                                + UNICODE_VERSION + " added, or a language this generator's"
                                + " KNOWN_TAILORING_LANGUAGES does not list yet? Decide which before"
                                + " teaching the generator to handle it either way.");
            }
        }
    }

    private static String firstWord(String s) {
        int space = s.indexOf(' ');
        return space < 0 ? s : s.substring(0, space);
    }

    private static int[] codePoints(String hexList) {
        String trimmed = hexList.trim();
        String[] parts = trimmed.split("\\s+");
        int[] result = new int[parts.length];
        for (int i = 0; i < parts.length; i++) {
            result[i] = Integer.parseInt(parts[i], 16);
        }
        return result;
    }

    /** {@code <range-or-code-point> ; <property> # <comment>}. Only {@code Cased} and
     *  {@code Case_Ignorable} are read — the two the {@code Final_Sigma} condition in the Unicode
     *  core specification's Default Case Algorithms section is stated over. */
    private static void parseDerivedCoreProperties(Path path, List<int[]> cased, List<int[]> caseIgnorable)
            throws IOException {
        for (String rawLine : Files.readAllLines(path, StandardCharsets.UTF_8)) {
            String line = rawLine.replaceFirst("#.*", "");
            if (line.isBlank()) {
                continue;
            }
            String[] f = line.split(";", -1);
            if (f.length < 2) {
                continue;
            }
            String property = f[1].trim();
            if (!property.equals("Cased") && !property.equals("Case_Ignorable")) {
                continue;
            }
            String range = f[0].trim();
            int start;
            int end;
            int dots = range.indexOf("..");
            if (dots >= 0) {
                start = Integer.parseInt(range.substring(0, dots), 16);
                end = Integer.parseInt(range.substring(dots + 2), 16);
            } else {
                start = Integer.parseInt(range, 16);
                end = start;
            }
            (property.equals("Cased") ? cased : caseIgnorable).add(new int[] {start, end});
        }
    }

    /** The full mapping where {@code SpecialCasing.txt} states one, otherwise the simple mapping
     *  where {@code UnicodeData.txt} states one, otherwise absent — absent means "maps to itself",
     *  which is every code point this table does not mention. */
    private static Map<Integer, int[]> mergeMappings(Map<Integer, Integer> simple, Map<Integer, int[]> full) {
        Map<Integer, int[]> merged = new TreeMap<>(simple.entrySet().stream()
                .collect(java.util.stream.Collectors.toMap(Map.Entry::getKey, e -> new int[] {e.getValue()})));
        merged.putAll(full);
        return merged;
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

    private static String render(Map<Integer, int[]> lower, Map<Integer, int[]> upper,
            Map<Integer, int[]> finalSigmaLower, List<int[]> cased, List<int[]> caseIgnorable,
            String unicodeDataSha256, String specialCasingSha256, String derivedCorePropertiesSha256) {
        StringBuilder out = new StringBuilder();
        out.append("package souther.runtime;\n\n");
        out.append("/**\n");
        out.append(" * The default case conversion tables ADR-0119 reads: Unicode ").append(UNICODE_VERSION)
                .append(", untailored full mapping.\n");
        out.append(" *\n");
        out.append(" * <p>Generated from Unicode ").append(UNICODE_VERSION).append("'s {@code UnicodeData.txt}, ")
                .append("{@code SpecialCasing.txt} and {@code DerivedCoreProperties.txt}")
                .append(" ({@code https://www.unicode.org/Public/").append(UNICODE_VERSION).append("/ucd/})")
                .append(" by {@code bin/GenerateCaseTables.java}. DO NOT EDIT — regenerate on a Unicode\n");
        out.append(" * version bump with {@code java bin/GenerateCaseTables.java <ucd-directory>}, which this file's\n");
        out.append(" * source checksums let a reviewer confirm ran against the version it claims.\n");
        out.append(" *\n");
        out.append(" * <p>SHA-256, of the three input files as downloaded:\n");
        out.append(" * <ul>\n");
        out.append(" * <li>UnicodeData.txt: {@code ").append(unicodeDataSha256).append("}\n");
        out.append(" * <li>SpecialCasing.txt: {@code ").append(specialCasingSha256).append("}\n");
        out.append(" * <li>DerivedCoreProperties.txt: {@code ").append(derivedCorePropertiesSha256).append("}\n");
        out.append(" * </ul>\n");
        out.append(" */\n");
        out.append("final class CaseTables {\n\n");
        out.append("    private CaseTables() {}\n\n");
        out.append(DECODER_SOURCE);

        renderMapping(out, "LOWER", "lowercase", lower);
        renderMapping(out, "UPPER", "uppercase", upper);
        renderFinalSigma(out, finalSigmaLower);
        renderRanges(out, "CASED", "Cased", cased);
        renderRanges(out, "CASE_IGNORABLE", "Case_Ignorable", caseIgnorable);

        out.append("}\n");
        return out.toString();
    }

    /** {@link #LOWER}/{@link #UPPER}/{@link #FINAL_SIGMA} decode this way, and the ranges tables
     *  decode themselves; kept as one block of ordinary, reviewed Java rather than generated, since
     *  it is decoding logic, not Unicode data — a literal {@code int[][]} large enough to hold
     *  Unicode's full mapping does not fit the JVM's 64&nbsp;KB per-method bytecode limit as an
     *  array-literal initializer, so the data is a compact string constant instead, decoded once
     *  here. */
    private static final String DECODER_SOURCE = """
                /** A code point and the code point(s) it maps to — more than one for a Unicode
                 *  expansion such as {@code ß} → {@code SS}. */
                record Mapping(int[] codePoints, int[][] mapped) {}

                /** Decodes a "{@code <cp>:<mapped>[+<mapped>...] ...}" string — hex code points, space
                 *  separated entries, {@code +} joining a multi-code-point mapping — sorted by
                 *  {@code <cp>} so a lookup can binary search it. */
                private static Mapping decodeMapping(String data) {
                    String[] tokens = data.split(" ");
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

                /** Decodes a "{@code <start>-<end> ...}" string of sorted, non-overlapping inclusive
                 *  hex ranges into the parallel {@code [starts, ends]} arrays a lookup binary searches. */
                private static int[][] decodeRanges(String data) {
                    String[] tokens = data.split(" ");
                    int[] starts = new int[tokens.length];
                    int[] ends = new int[tokens.length];
                    for (int i = 0; i < tokens.length; i++) {
                        int dash = tokens[i].indexOf('-');
                        starts[i] = Integer.parseInt(tokens[i].substring(0, dash), 16);
                        ends[i] = Integer.parseInt(tokens[i].substring(dash + 1), 16);
                    }
                    return new int[][] {starts, ends};
                }

            """.stripIndent();

    private static void renderMapping(StringBuilder out, String name, String word, Map<Integer, int[]> mapping) {
        out.append("    /** Unicode 18.0.0's untailored full ").append(word).append(" mapping (").append(mapping.size())
                .append(" code points with a non-identity mapping; every other code point maps to itself). */\n");
        out.append("    static final Mapping ").append(name).append(" = decodeMapping(\"")
                .append(encodeMapping(mapping)).append("\");\n\n");
    }

    private static void renderFinalSigma(StringBuilder out, Map<Integer, int[]> finalSigmaLower) {
        out.append("    /** Code points whose {@link #LOWER} mapping is the untailored default, overridden by this\n");
        out.append("     *  mapping's result when the code point sits at the end of a cased run (Unicode's\n");
        out.append("     *  {@code Final_Sigma} condition) — Unicode 18.0.0 states exactly one such entry, Greek\n");
        out.append("     *  capital sigma, mapping to one code point, but nothing here assumes that arity: this\n");
        out.append("     *  is the same {@link Mapping} shape {@link #LOWER}/{@link #UPPER} use, read the same way,\n");
        out.append("     *  so a future Unicode version's wider Final_Sigma entry needs only regeneration. */\n");
        out.append("    static final Mapping FINAL_SIGMA = decodeMapping(\"").append(encodeMapping(finalSigmaLower))
                .append("\");\n\n");
    }

    private static void renderRanges(StringBuilder out, String name, String property, List<int[]> ranges) {
        out.append("    /** {@code ").append(property).append("} (the property Unicode's {@code Final_Sigma}\n");
        out.append("     *  condition is stated over), as sorted non-overlapping inclusive ranges: index 0 is\n");
        out.append("     *  starts, index 1 is ends. */\n");
        out.append("    static final int[][] ").append(name).append(" = decodeRanges(\"")
                .append(encodeRanges(ranges)).append("\");\n\n");
    }

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

    private static String encodeRanges(List<int[]> ranges) {
        StringBuilder sb = new StringBuilder();
        for (int[] r : ranges) {
            if (!sb.isEmpty()) {
                sb.append(' ');
            }
            sb.append(hex(r[0])).append('-').append(hex(r[1]));
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
