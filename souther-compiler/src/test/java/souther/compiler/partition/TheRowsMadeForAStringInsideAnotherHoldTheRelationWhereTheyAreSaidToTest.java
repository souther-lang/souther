package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.evaluate.BoundUnderEvaluation;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;
import souther.compiler.semantics.CaseMapping;
import souther.compiler.semantics.StringContainment;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row made for a class of one string standing inside another is one the relation holds at, or
 * fails at, as the class says — whichever string looks for the other and however the strings are
 * converted before.
 *
 * <p>The rows are asked of the compiler as a person is given them and run through the run time's
 * own conversion, rather than read off the language the class was drawn over: a class drawn
 * over a string the conversion makes something else of would show up as a row the relation does
 * not hold at, and a class said never to hold would show up as a row some value of the partner
 * does hold at.
 *
 * <p>{@code String.contains(inner, outer)}: the string looked for is the first, as the library
 * writes the strings it works on last.
 */
class TheRowsMadeForAStringInsideAnotherHoldTheRelationWhereTheyAreSaidToTest {

    private static final Pattern ROW = Pattern.compile(
            "\\|\\s+\"([^\"]*)\"\\s*:\\s*\\(In \\{ name = \"((?:[^\"\\\\]|\\\\.)*)\","
                    + " code = Code\\(\"((?:[^\"\\\\]|\\\\.)*)\"\\) \\}\\)");

    private record Made(String label, String name, String code) {

        boolean isSaidToHold() {
            return label.contains(" can be ");
        }

        boolean isSaidNeverToHold() {
            return label.contains(" is never ");
        }
    }

    private static String source(String function, boolean nameHoldsTheCode, boolean lowercased,
                                 String codes) {
        String code = lowercased ? "String.lowercase(i.code.value)" : "i.code.value";
        String name = lowercased ? "String.lowercase(i.name)" : "i.name";
        return """
                module demo

                data Code = String
                    invariant String.matches("%s", value)

                data In = { name: String, code: Code }

                behavior f : (i: In) -> Bool
                let f (i) = String.%s(%s, %s)
                """.formatted(codes, function, nameHoldsTheCode ? code : name,
                nameHoldsTheCode ? name : code);
    }

    private static String unescaped(String written) {
        StringBuilder out = new StringBuilder();
        for (int at = 0; at < written.length(); at++) {
            char c = written.charAt(at);
            if (c != '\\') {
                out.append(c);
                continue;
            }
            char next = written.charAt(++at);
            switch (next) {
                case 't' -> out.append('\t');
                case 'n' -> out.append('\n');
                case 'r' -> out.append('\r');
                case 'u' -> {
                    int close = written.indexOf('}', at);
                    out.appendCodePoint(Integer.parseInt(written.substring(at + 2, close), 16));
                    at = close;
                }
                default -> out.append(next);
            }
        }
        return out.toString();
    }

    private static List<Made> made(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String block = GeneratedRows.of(compilation, null, null,
                SourceRendering.namedByIdentity(compilation.texts())).text();
        List<Made> out = new ArrayList<>();
        Matcher found = ROW.matcher(block);
        while (found.find()) {
            out.add(new Made(found.group(1), unescaped(found.group(2)),
                    unescaped(found.group(3))));
        }
        return out;
    }

    private static String reported(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE));
    }

    /** The first value the document gives {@code field}, which is the whole document's. */
    private static String firstValueOf(String field, String json) {
        Matcher found = Pattern.compile("\"" + field + "\"\\s*:\\s*\"([^\"]*)\"").matcher(json);
        return found.find() ? found.group(1) : null;
    }

    private static String converted(boolean lowercased, String text) {
        return lowercased ? BoundUnderEvaluation.mapped(CaseMapping.LOWERCASE, text) : text;
    }

    /** Whether the relation holds of the values {@code name} and {@code code}. */
    private static boolean holds(StringContainment where, boolean nameHoldsTheCode,
                                 boolean lowercased, String name, String code) {
        String inner = converted(lowercased, nameHoldsTheCode ? code : name);
        String outer = converted(lowercased, nameHoldsTheCode ? name : code);
        return where.holds(inner, outer);
    }

    private static void check(String function, StringContainment where, boolean nameHoldsTheCode,
                              boolean lowercased, String codes, List<String> everyCode) {
        check(function, where, nameHoldsTheCode, lowercased, codes, everyCode, true);
    }

    /** @param aRowIsMade whether a row said to hold is asked for, which a partner the conversion
     *                    does not map exactly gives none of */
    private static void check(String function, StringContainment where, boolean nameHoldsTheCode,
                              boolean lowercased, String codes, List<String> everyCode,
                              boolean aRowIsMade) {
        String source = source(function, nameHoldsTheCode, lowercased, codes);
        List<Made> rows = made(source);
        if (aRowIsMade) {
            assertTrue(rows.stream().anyMatch(Made::isSaidToHold),
                    () -> "a row is made: " + source);
        }
        for (Made row : rows) {
            if (row.isSaidToHold()) {
                assertTrue(holds(where, nameHoldsTheCode, lowercased, row.name(), row.code()),
                        () -> function + " holds at " + row + " in " + source);
            }
            if (row.isSaidNeverToHold()) {
                for (String code : everyCode) {
                    assertFalse(holds(where, nameHoldsTheCode, lowercased, row.name(), code),
                            () -> function + " holds at " + row.name() + " against " + code
                                    + ", said never to: " + source);
                }
            }
        }
    }

    @Test
    void aStringHoldingTheOtherHasRowsItHoldsAtAndFailsAt() {
        for (boolean lowercased : new boolean[] {false, true}) {
            check("contains", StringContainment.ANYWHERE, true, lowercased, "JP|US",
                    List.of("JP", "US"));
            check("startsWith", StringContainment.AT_THE_START, true, lowercased, "JP|US",
                    List.of("JP", "US"));
            check("endsWith", StringContainment.AT_THE_END, true, lowercased, "JP|US",
                    List.of("JP", "US"));
        }
    }

    @Test
    void aStringInsideTheOtherHasRowsItHoldsAtAndFailsAt() {
        for (boolean lowercased : new boolean[] {false, true}) {
            check("contains", StringContainment.ANYWHERE, false, lowercased, "JP|US",
                    List.of("JP", "US"));
            check("startsWith", StringContainment.AT_THE_START, false, lowercased, "JP|US",
                    List.of("JP", "US"));
            check("endsWith", StringContainment.AT_THE_END, false, lowercased, "JP|US",
                    List.of("JP", "US"));
        }
    }

    /**
     * A value of the partner that a conversion makes more of than one code point is a string the
     * strings it is looked for in or inside are not shown for: a row said never to hold must not
     * be one the conversion makes hold, and the report names the operation whose image is not
     * shown.
     */
    @Test
    void aPartnerValueTheConversionLengthensIsNeverTakenForOneItDoesNotHoldAt() {
        for (String codes : List.of("İ|X", "ß|SS", "ǅ|X")) {
            List<String> every = List.of(codes.split("\\|"));
            check("contains", StringContainment.ANYWHERE, true, true, codes, every, false);
            check("contains", StringContainment.ANYWHERE, false, true, codes, every, false);
            String json = reported(source("contains", true, true, codes));
            assertTrue(json.contains("\"imagesNotShown\""), () -> "the image is named: " + codes);
            assertTrue(json.contains("String.lowercase"), () -> "and it is lowercase: " + codes);
            // What no row was made for is left owed, and not counted as covered: the question of
            // which class this rule puts those values in stays open at the position.
            assertTrue(json.contains("relation_shown_over_a_region"),
                    () -> "the region left open is reported: " + codes);
            assertTrue(json.contains("\"leftOpen\""), () -> "and says what it leaves: " + codes);
            assertEquals("partial", firstValueOf("status", json),
                    () -> "and the measure is not complete: " + codes);
            assertEquals("not_satisfied", firstValueOf("adequacy", json),
                    () -> "nor adequate: " + codes);
        }
    }

    @Test
    void theUnescapingOfARowReadsWhatTheBlockWrites() {
        assertEquals("\t", unescaped("\\t"));
        assertEquals("a\"b", unescaped("a\\\"b"));
        assertEquals("İ", unescaped("\\u{130}"));
    }
}
