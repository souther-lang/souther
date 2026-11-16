package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A number moved up is no value at the last one of its type, so what a comparison reads of a
 * shifted {@code Int} or {@code Date} does not reach every value, with a way that keeps a value off
 * numbers or without one. Over {@code Decimal}, which has no last value, the same shapes are read.
 */
class AShiftOfAnIntOrADateIsNotReadOverEveryValueWhateverTheWayIsTest {

    private static final String NOT_SHOWN = "not shown to reach every value";

    private static String report(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static String comparison(String type, String body) {
        return report("""
                module p
                behavior f : (h: %1$s, d: %1$s, s: %1$s) -> Bool
                let f = %2$s
                """.formatted(type, body));
    }

    /** Whether the report says of {@code place} that what it is related to is not shown to reach
     *  every value of it. */
    private static boolean notShownAt(String human, String place) {
        return human.lines().anyMatch(line -> line.contains(NOT_SHOWN)
                && line.contains("about `" + place + "`"));
    }

    /** No way here keeps a value off a number: what stays unread is what the shift leaves of the
     *  run. */
    @Test
    void aShiftBesideAComparisonIsUnreadOverAnIntAndADateNotADecimal() {
        String decimal = comparison("Decimal", "(h, d, s) -> (if d >= h then d + 1.0m else d) >= s");
        String integer = comparison("Int", "(h, d, s) -> (if d >= h then d + 1 else d) >= s");
        String date = comparison("Date",
                "(h, d, s) -> (if d >= h then Date.addDays(1, d) else d) >= s");

        assertFalse(notShownAt(decimal, "d"), decimal);
        assertTrue(notShownAt(integer, "d"), integer);
        assertTrue(notShownAt(date, "d"), date);
    }

    /**
     * What a way's statements leave of a number is proved only for numbers of a type with no ends.
     * Each proof moves a number by an amount, or writes it at a value worked out of others, and at
     * the last value of an {@code Int} the number moved up is no value: so the shapes that are
     * read over {@code Decimal} are not shown read over {@code Int}.
     */
    @Test
    void theShapesReadOverEveryDecimalAreNotReadOverEveryInt() {
        for (String type : new String[] {"Decimal", "Int"}) {
            boolean read = type.equals("Decimal");
            String one = read ? "1.0m" : "1";
            String walk = report("""
                    module p
                    let free (hs: Set<%1$s>, d: %1$s): Bool = Bool.not(Set.contains(d, hs))
                    behavior f : (hs: Set<%1$s>, from: %1$s) -> %1$s
                    let f (hs, from) = [ from, from + %2$s, from + %2$s + %2$s ]
                        |> List.find(d -> free(hs, d)) |> Option.withDefault(from)
                    """.formatted(type, one));
            String arms = comparison(type, "(h, d, s) -> (if d /= h then d else if d + " + one
                    + " /= h then d + " + one + " else d) >= s");

            assertEquals(!read, notShownAt(walk, "from"), type + walk);
            assertEquals(!read, notShownAt(walk, "hs[*]"), type + walk);
            assertEquals(!read, notShownAt(arms, "d"), type + arms);
            assertEquals(!read, notShownAt(arms, "h"), type + arms);
        }
    }
}
