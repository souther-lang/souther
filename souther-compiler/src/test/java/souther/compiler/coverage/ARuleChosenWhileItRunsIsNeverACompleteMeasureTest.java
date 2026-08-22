package souther.compiler.coverage;

import org.junit.jupiter.api.Test;

import souther.compiler.observe.MeasurementStatus;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A fork deciding by a rule chosen while the behavior runs is never a complete measure of its arms.
 *
 * <p>One call site, and as many rules as the choice has arms. What an arm of such a fork is owed for
 * is one rule, and a row that took an arm under one of them says nothing about the arm another would
 * have taken — so a count over the call site is a count over however many rules reach it.
 *
 * <p>Asked of what the measure comes to and not of how it gets there. Today the rows of such a model
 * cannot be read at all and the arms come back unavailable, which is an honest answer; the day they
 * can be read, the answer owed is that the rules could not be told apart. Either is fine and
 * {@code COMPLETE} is not, which is what this holds.
 */
class ARuleChosenWhileItRunsIsNeverACompleteMeasureTest {

    private static final String MODULE = "example.chosen";

    private static final String MODEL = """
            module example.chosen

            data Count = Int

            behavior tally : (positive: Bool, xs: List<Int>) -> Count
                constructs Count
            let tally (positive, xs) = {
                let p: (Int) -> Bool =
                    if positive then (x) -> x > 0 else (x) -> x < 0

                Count(List.length(List.filter(p, xs)))
            }

            example tally
                | "the rule that keeps" : (true,  [ 1 ]) -> Count(1)
                | "the rule that drops" : (false, [ 1 ]) -> Count(0)
            """;

    @Test
    void itsArmsAreNeverCountedAsAWholeMeasure() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Adequacy.BranchEvidence tally = compilation.db()
                .ask(new Adequacy.BranchCoverage(MODULE)).value().get("tally");
        assertNotNull(tally, "the model under test compiles");

        assertNotEquals(MeasurementStatus.COMPLETE, tally.status(),
                () -> "one call site, and a rule chosen while it runs: " + tally.status()
                        + " over " + tally.all().size() + " arm(s)");
    }
}
