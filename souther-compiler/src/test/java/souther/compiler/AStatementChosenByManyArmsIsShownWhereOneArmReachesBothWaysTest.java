package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A statement chosen among more than two arms, or among arms written inside arms, comes out each
 * way at a value where some arm does: a row that takes the arm has the statement come out as the
 * arm's relation does. What it never says is that no arm reaches a way, which is a claim about the
 * rows of arms nobody read.
 */
class AStatementChosenByManyArmsIsShownWhereOneArmReachesBothWaysTest {

    private static final String NOT_SHOWN = "not shown to reach every value";

    private static String report(String body) {
        Compilation compilation = Compilation.ofSource("""
                module p
                behavior f : (h: Decimal, d: Decimal, s: Decimal) -> Bool
                let f (h, d, s) = %s
                """.formatted(body), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static boolean notShownAt(String human, String place) {
        return human.lines().anyMatch(line -> line.contains(NOT_SHOWN)
                && line.contains("about `" + place + "`"));
    }

    /** The first arm keeps {@code d} off {@code h}, so reaches every {@code s} both ways; the
     *  third arm, past {@code d == h} and {@code d + 1 == h}, is one no row takes. */
    @Test
    void aValueChosenByACaseAndItsDenialInsideAnotherIsComparedOverEveryValue() {
        String human = report(
                "(if d /= h then d else if d + 1.0m /= h then d + 1.0m else d) >= s");

        assertFalse(notShownAt(human, "d"), human);
        assertFalse(notShownAt(human, "s"), human);
        assertFalse(notShownAt(human, "h"), human);
    }

    /** The way to the comparison states only differences ({@code d /= h}, {@code d == h}), and a
     *  row moved by one amount in every number it names meets them as it did: a value of
     *  {@code d} or of {@code s} is taken by a row wherever it is. */
    @Test
    void aWayStatingOnlyDifferencesTakesNoValueOfTheNumbersItNames() {
        String human = report("([ d, d + 1.0m ] |> List.find(x -> x /= h)"
                + " |> Option.withDefault(d)) >= s");

        assertFalse(notShownAt(human, "d"), human);
        assertFalse(notShownAt(human, "s"), human);
        assertFalse(notShownAt(human, "h"), human);
    }

    /** The same with a third arm a row can take. */
    @Test
    void aThirdArmARowCanTakeChangesNothingOfWhatTheFirstReaches() {
        String human = report(
                "(if d /= h then d else if d + 5.0m /= h then d + 1.0m else d + 2.0m) >= s");

        assertFalse(notShownAt(human, "d"), human);
        assertFalse(notShownAt(human, "s"), human);
        assertFalse(notShownAt(human, "h"), human);
    }
}
