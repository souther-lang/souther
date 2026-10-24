package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Count;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.partition.Level;
import souther.compiler.partition.PointRole;
import souther.compiler.partition.ReachabilityGap;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
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
 * <p>Conditions of several ways that turn on no position in common are looked along each of their
 * alternatives once, and not along every way of taking them together: a rule closing one
 * alternative of the first leaves the second alternative of it looked along, however many
 * conditions stand beside it.
 *
 * <p>And where the ways are more than are looked along, the ones the figure lets through are
 * looked along first and the way whole past them; a row of the way whole says which conditions it
 * was not split at, and at which figure — since along one of them a row would have been composed
 * against more.
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

    /** Five conditions of two ways each, which taken together are more ways than are looked
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

    /** The same, with the first alternative of the first condition closed by a rule: taken
     *  together with the others, the first sixteen ways would all take it. */
    private static final String TOO_MANY_FIRST_CLOSED = """
            module example.either

            data N = Int
                invariant value >= 0 && value <= 100

            data Yes
            data No

            behavior f : (a: N, b: N, c: N, d: N, e: N, g: N, h: N, i: N, j: N, k: N, n: N)
                -> Yes | No

            let f (a, b, c, d, e, g, h, i, j, k, n) = {
                guard a == 0 else No
                guard a > 0 || b > 0 else No
                guard c > 0 || d > 0 else No
                guard e > 0 || g > 0 else No
                guard h > 0 || i > 0 else No
                guard j > 0 || k > 0 else No
                if n > 5 then Yes else No
            }
            """;

    /**
     * One condition of seventeen ways on one position, every way of which but the last the
     * declarations close — a level past what {@code N} holds, which the statements of the way do
     * not contradict: more ways than are looked along, and the one that reaches past them.
     *
     * <p>That the ways stay open rests on the walk not reading the declarations. That more ways
     * than are looked along are looked along whole is held without it, by
     * {@code AChoiceTheNumbersContradictIsNoOpenWayTest}, and this holds what the account says of
     * it: were the walk to read the declarations, these ways would need closing by something it
     * does not read.
     */
    private static final String ONE_PAST_THE_FIGURE = """
            module example.either

            data N = Int
                invariant value >= 0 && value <= 100

            data Yes
            data No

            behavior f : (a: N, n: N) -> Yes | No

            let f (a, n) = {
                guard ALTERNATIVES_OF_A else No
                if n > 5 then Yes else No
            }
            """.replace("ALTERNATIVES_OF_A", alternatives("a"));

    /**
     * Two such conditions, on two positions: the only way a row takes is the last of both, and
     * the ways looked along hold each alternative of each beside the other's first, never the
     * last of both together.
     */
    private static final String PAST_THE_FIGURE = """
            module example.either

            data N = Int
                invariant value >= 0 && value <= 100

            data Yes
            data No

            behavior f : (a: N, b: N, n: N) -> Yes | No

            let f (a, b, n) = {
                guard ALTERNATIVES_OF_A else No
                guard ALTERNATIVES_OF_B else No
                if n > 5 then Yes else No
            }
            """.replace("ALTERNATIVES_OF_A", alternatives("a"))
            .replace("ALTERNATIVES_OF_B", alternatives("b"));

    private static final Count BEHIND_THE_FORK = Count.of(5);

    /** {@code name} at as many levels past the top of {@code N} as ways are looked along, and then
     *  at nought. */
    private static String alternatives(String name) {
        List<String> out = new ArrayList<>();
        for (int each = 1; each <= CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG.maximum(); each++) {
            out.add(name + " == " + (100 + each));
        }
        out.add(name + " == 0");
        return String.join(" || ", out);
    }

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

    /**
     * Conditions on different positions are each looked along, and a row along one way of them is
     * offered.
     */
    @Test
    void independentConditionsAreLookedAlongAndARowIsOffered() {
        List<ItemAssessment.Owed> owed = pointsOfTheInnerLine(TOO_MANY);
        assertFalse(owed.isEmpty(), "the line behind the guards is owed rows");
        for (ItemAssessment.Owed item : owed) {
            assertTrue(item.searches().rowToOffer().isPresent(),
                    () -> "a row along one of the ways looked along is offered: "
                            + item.searches());
            assertTrue(lookedAlongWhole(item).isEmpty(),
                    () -> "and every alternative was looked along: " + item.searches());
        }
    }

    /**
     * An alternative a rule closes is looked along beside the others, and the other alternative of
     * the same condition is looked along as well — not left behind every way of taking the
     * conditions beside it together.
     */
    @Test
    void anAlternativeARuleClosesLeavesTheOtherLookedAlong() {
        List<ItemAssessment.Owed> owed = pointsOfTheInnerLine(TOO_MANY_FIRST_CLOSED);
        assertFalse(owed.isEmpty(), "the line behind the guards is owed rows");
        for (ItemAssessment.Owed item : owed) {
            assertTrue(item.searches().rowToOffer().isPresent(),
                    () -> "a row along the open alternative is offered: " + item.searches());
            assertTrue(lookedAlongWhole(item).isEmpty(),
                    () -> "and no way was looked along whole: " + item.searches());
        }
    }

    /**
     * Where the ways of one condition are more than are looked along, each alternative of it is
     * still looked along once: the one a row can take, though it comes after the figure, is
     * offered a row.
     */
    @Test
    void anAlternativePastTheFigureOfOneConditionIsStillLookedAlong() {
        List<ItemAssessment.Owed> owed = pointsOfTheInnerLine(ONE_PAST_THE_FIGURE);
        assertFalse(owed.isEmpty(), "the line behind the guard is owed rows");
        for (ItemAssessment.Owed item : owed) {
            assertTrue(item.searches().rowToOffer().isPresent(),
                    () -> "a row along the last alternative is offered: " + item.searches());
            // The last alternative is the one that holds a at nought, and the row is the one that
            // goes along it.
            assertEquals("N(0)",
                    item.searches().rowToOffer().orElseThrow().row().inputs().getFirst().text(),
                    () -> "and it is a row with a at nought: " + item.searches());
            assertTrue(lookedAlongWhole(item).isEmpty(),
                    () -> "and nothing was left to be looked along whole: " + item.searches());
        }
    }

    /**
     * Where the ways of conditions on two positions are more than are looked along, and the row
     * is along the last alternative of both, the way is looked along whole past them, and the
     * account of what that came to says which conditions it was not split at.
     */
    @Test
    void pastTheFigureTheAccountSaysWhichConditionsTheWayWasNotSplitAt() {
        List<ItemAssessment.Owed> owed = pointsOfTheInnerLine(PAST_THE_FIGURE);
        assertFalse(owed.isEmpty(), "the line behind the guards is owed rows");
        for (ItemAssessment.Owed item : owed) {
            List<ReachabilityGap.LookedAlongWhole> said = lookedAlongWhole(item);
            assertFalse(said.isEmpty(), () -> "the way was looked along whole and says so: "
                    + item.searches());
            assertTrue(said.stream().allMatch(gap ->
                            gap.figure() == CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG),
                    () -> "at the figure for how many ways are looked along: " + said);
        }
    }

    /** What the searches at {@code item} said of a way looked along whole. */
    private static List<ReachabilityGap.LookedAlongWhole> lookedAlongWhole(
            ItemAssessment.Owed item) {
        List<ReachabilityGap.LookedAlongWhole> said = new ArrayList<>();
        for (ItemAssessment.Attempt each : item.searches().each()) {
            if (each instanceof ItemAssessment.Attempt.Searched searched) {
                searched.uncomposed().onTheWay().stream()
                        .filter(ReachabilityGap.LookedAlongWhole.class::isInstance)
                        .map(ReachabilityGap.LookedAlongWhole.class::cast)
                        .forEach(said::add);
            }
        }
        return said;
    }

    /** What was searched for at each point of the line behind the conditions of several ways. */
    private static List<ItemAssessment.Owed> pointsOfTheInnerLine(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        List<BorderAssessment> edges = compilation.db()
                .ask(new Adequacy.BoundarySearch("example.either", "f")).value();
        assertNotNull(edges, "the lines of this behavior were searched");
        List<ItemAssessment.Owed> out = new ArrayList<>();
        for (BorderAssessment each : edges) {
            if (each.border().origin().comparisonAt().isEmpty()
                    || !(each.border().cut().at() instanceof Level.OnACarrier(_, var at)
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
