package souther.compiler.coverage;

import org.junit.jupiter.api.Test;

import souther.compiler.check.TypeChecker;
import souther.compiler.core.Core;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A line is owed for the comparison that was written, not for the fork that tests it.
 *
 * <p>The two are usually one construct, and where they are the difference does not show. What makes
 * them separate questions is that a condition need not be written where the fork is: it can apply a
 * function parameter, and then the predicate belongs to whoever called the helper. Keyed on the fork,
 * two predicates written separately would be one line — the accounting for a helper's own comparison
 * copied twice, applied to two comparisons each written once.
 *
 * <p>That case cannot be exercised from a source today, and the reason is worth writing down rather
 * than leaving to be rediscovered. Applying a function parameter reduces to the predicate's body
 * under a binding for its argument, so the condition of the fork is a {@code LetIn};
 * {@link CoverageSites} numbers a comparison only where the condition is one or is built from
 * {@code &&} and {@code ||}, and it does not descend a binding. An injected predicate therefore gets
 * no comparison site at all, and there is nothing for an identity to be right or wrong about. The
 * rows below are the two cases that do arise, and they hold whichever key is used — what keeps the
 * third from arising is one line in a walk, which is why the comparison carries its own origin rather
 * than borrowing the fork's.
 */
class AComparisonBelongsToWhoWroteItNotToTheForkTestingItTest {

    @Test
    void aHelpersOwnComparisonIsOneLineHoweverOftenItIsCalled() {
        List<CoverageSites.Obligation> lines = comparisonsOf("""
                module example.banding

                data Amount = Int
                    invariant value >= 0

                data Small
                data Large
                data Size = Small | Large

                data Left
                data Right
                data Side = Left | Right

                let band (a: Amount): Size =
                    if a.value <= 100 then Small else Large

                behavior twice : (side: Side, a: Amount) -> Size
                let twice (side, a) =
                    match side with
                        | Left -> band(a)
                        | Right -> band(a)
                """);

        assertEquals(2, lines.size(), "the expansion put a copy of the comparison at each call");
        assertEquals(1, lines.stream().distinct().count(),
                "and one comparison was written, so one row at its value answers for both");
    }

    /** Two comparisons of one condition are two lines, and stay two through the copies. Without this
     * the row above would pass on a key that had collapsed every comparison of a fork into one. */
    @Test
    void twoComparisonsOfOneConditionStayTwoLines() {
        List<CoverageSites.Obligation> lines = comparisonsOf("""
                module example.window

                data Amount = Int
                    invariant value >= 0

                data In
                data Out
                data Where = In | Out

                data Left
                data Right
                data Side = Left | Right

                let window (a: Amount): Where =
                    if a.value >= 10 && a.value <= 100 then In else Out

                behavior twice : (side: Side, a: Amount) -> Where
                let twice (side, a) =
                    match side with
                        | Left -> window(a)
                        | Right -> window(a)
                """);

        assertEquals(4, lines.size(), "two comparisons, each copied at each of the two calls");
        assertEquals(2, lines.stream().distinct().count(),
                "over the two comparisons the condition is written with");
    }

    private static List<CoverageSites.Obligation> comparisonsOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        TypeChecker.Checked checked = compilation.db()
                .ask(new Bodies.Checked(compilation.modules().get(0))).value();
        assertNotNull(checked, "the model under test compiles");
        Map<String, Core> bodies = checked.behaviorBodies();
        CoverageSites.Plan plan = CoverageSites.of("model.sou", bodies);
        return plan.sites().stream()
                .filter(site -> site.kind() == CoverageSites.Site.Kind.COMPARISON)
                .map(CoverageSites.Site::obligation)
                .toList();
    }
}
