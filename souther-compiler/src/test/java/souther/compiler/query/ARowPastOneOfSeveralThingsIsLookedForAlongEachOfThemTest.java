package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Count;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.partition.Level;
import souther.compiler.partition.PointRole;
import souther.compiler.partition.ReachabilityGap;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row past a condition that came out one of several ways is looked for along each of them, and
 * one that stands at the point along one of them is offered for it.
 *
 * <p>{@code x > 0 || y > 0} coming out true names neither, so the way whole narrows neither: a
 * composer handed only that writes whatever the rules leave, which is the bottom of both and takes
 * the other branch. Along one alternative the row is composed with {@code x} above nought, and the
 * run is what says it reached the line behind the fork.
 *
 * <p>And where the ways the conditions of several ways split it into are more than are looked
 * along, the way is looked along whole and the row's account says which conditions it was not
 * split at, and at which figure — since along one of them a row would have been composed against
 * more.
 */
class ARowPastOneOfSeveralThingsIsLookedForAlongEachOfThemTest {

    private static final String EITHER = """
            module example.either

            data N = Int
                invariant value >= 0 && value <= 100

            data Yes
            data No

            behavior f : (x: N, y: N, n: N) -> Yes | No

            let f (x, y, n) =
                if x > 0 || y > 0
                then (if n > 5 then Yes else No)
                else No
            """;

    /** Five conditions of two ways each, which split the way into more ways than are looked
     *  along. */
    private static final String TOO_MANY = """
            module example.either

            data N = Int
                invariant value >= 0 && value <= 100

            data Yes
            data No

            behavior f : (a: N, b: N, c: N, d: N, e: N, g: N, h: N, i: N, j: N, k: N, n: N)
                -> Yes | No

            let f (a, b, c, d, e, g, h, i, j, k, n) = {
                guard a > 0 || b > 0 else No
                guard c > 0 || d > 0 else No
                guard e > 0 || g > 0 else No
                guard h > 0 || i > 0 else No
                guard j > 0 || k > 0 else No
                if n > 5 then Yes else No
            }
            """;

    private static final Count BEHIND_THE_FORK = Count.of(5);

    @Test
    void aRowAlongOneAlternativeIsOfferedForEveryPointBehindIt() {
        List<ItemAssessment.Owed> owed = pointsOfTheInnerLine(EITHER);
        assertFalse(owed.isEmpty(), "the line behind the fork is owed rows");
        for (ItemAssessment.Owed item : owed) {
            assertTrue(item.searches().rowToOffer().isPresent(),
                    () -> "a row along one alternative stands at the point and is offered: "
                            + item.searches());
        }
    }

    @Test
    void pastTheFigureTheAccountSaysWhichConditionsTheWayWasNotSplitAt() {
        List<ItemAssessment.Owed> owed = pointsOfTheInnerLine(TOO_MANY);
        assertFalse(owed.isEmpty(), "the line behind the guards is owed rows");
        for (ItemAssessment.Owed item : owed) {
            List<ReachabilityGap.LookedAlongWhole> said = new ArrayList<>();
            for (ItemAssessment.Attempt each : item.searches().each()) {
                if (each instanceof ItemAssessment.Attempt.Searched searched) {
                    searched.uncomposed().onTheWay().stream()
                            .filter(ReachabilityGap.LookedAlongWhole.class::isInstance)
                            .map(ReachabilityGap.LookedAlongWhole.class::cast)
                            .forEach(said::add);
                }
            }
            assertFalse(said.isEmpty(), () -> "the way was looked along whole and says so: "
                    + item.searches());
            assertTrue(said.stream().allMatch(gap ->
                            gap.figure() == CompositionBudget.WAYS_A_WAY_IS_SPLIT_INTO),
                    () -> "at the figure for how many ways a way is split into: " + said);
        }
    }

    /** What was searched for at each point of the line behind the conditions of several ways. */
    private static List<ItemAssessment.Owed> pointsOfTheInnerLine(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        List<BorderAssessment> edges = compilation.db()
                .ask(new Adequacy.BoundarySearch("example.either", "f")).value();
        assertNotNull(edges, "the lines of this behavior were searched");
        List<ItemAssessment.Owed> out = new ArrayList<>();
        for (BorderAssessment each : edges) {
            if (each.border().origin().comparisonAt().isEmpty()
                    || !(each.border().obligation().at() instanceof Level.OnACarrier(_, var at)
                            && at instanceof Count count
                            && count.compareTo(BEHIND_THE_FORK) == 0)) {
                continue;
            }
            for (PointRole role : PointRole.values()) {
                if (each.at(role) instanceof ItemAssessment.Owed owed) {
                    out.add(owed);
                }
            }
        }
        return out;
    }
}
