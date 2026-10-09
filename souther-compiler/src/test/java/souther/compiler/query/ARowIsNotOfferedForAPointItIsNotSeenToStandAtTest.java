package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Count;
import souther.compiler.partition.Generator;
import souther.compiler.partition.ObligationIdentity;
import souther.compiler.partition.PointRole;
import souther.compiler.partition.ReachabilityGap;
import souther.compiler.partition.RowDemand;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A gap in what the walk can say about the way costs rows, and never costs the truth about them.
 *
 * <p>The two halves of this are asymmetric on purpose, and the asymmetry is the design. What a
 * search composes a row against is however much of the way to the border this reading could state;
 * what says a row is a row for the point is the walk that reads any row at a point. So a condition
 * on the way that nothing could state makes rows harder to compose — and cannot make a row that
 * does not stand at a point be offered for it.
 *
 * <p>Held against a condition no composer writes a row for rather than one it composes against,
 * because that is the case the second half exists for. A condition of several ways is looked for
 * along each of them ({@link ARowPastOneOfSeveralThingsIsLookedForAlongEachOfThemTest}). A model whose way is understood composes a row that reaches and
 * the walk agrees with it; the run worth writing down is the one where the composer was told
 * nothing and guessed.
 *
 * <p>This is the test that goes on holding when a fork nothing here has learned to read arrives in
 * the language. What such a fork takes away is rows. What it may not take away is that an offered
 * row is one nothing saw standing somewhere else.
 */
class ARowIsNotOfferedForAPointItIsNotSeenToStandAtTest {

    /**
     * A comparison reached past a condition on a value the body works out, which no composer can
     * write.
     *
     * <p>What a product of {@code x} and {@code y} comes to is no form over them, so the condition
     * on it is a condition on a value no position holds, and there is no cut to narrow a search by.
     * The values the composer then writes at {@code x} and {@code y} are whatever their own rules
     * leave, which is the bottom of the run and takes the other branch — so a row carrying the value
     * the inner line is drawn at turns back above it.
     */
    private static final String MODEL = """
            module example.unspoken

            data N = Int
                invariant value >= 0 && value <= 100

            data Yes
            data No

            behavior f : (x: Int, y: Int, n: N) -> Yes | No

            let f (x, y, n) = {
                let area = x * y
                if area > 4
                then (if n > 5 then Yes else No)
                else No
            }
            """;

    /** Where the line behind the product is drawn, which is the one this is about. */
    private static final Count BEHIND_THE_PRODUCT = Count.of(5);

    /**
     * Every point of that line is owed a row and offered none, and the reason names the walk.
     *
     * <p>The point stays owed — it is one of the things this run was asked for a row at — and what
     * is missing is a row to offer, which is the honest answer where nothing composed one that
     * reaches. Offered anyway, the row would be a piece of work handed to somebody that does not do
     * what it says.
     */
    @Test
    void noRowIsOfferedWhereTheOneComposedWasNotSeenStandingThere() {
        List<ItemAssessment> owed = pointsOfTheInnerLine();
        assertFalse(owed.isEmpty(), "the line behind the product is owed rows");
        for (ItemAssessment item : owed) {
            assertTrue(((ItemAssessment.Owed) item).searches().rowToOffer().isEmpty(),
                    "nothing composed a row that reaches this point, so none is offered");
            assertEquals(Generator.UnresolvedCombination.Reason.NO_CERTIFIED_WITNESS,
                    wordOf((ItemAssessment.Owed) item),
                    "and the reason is what the walk that reads a row said, not what the search"
                            + " managed to compose");
        }
    }

    /**
     * And the way to it is on the account, with the composer saying it placed nothing for the
     * condition — which is what made it guess.
     */
    @Test
    void theWayToItSaysNothingWasComposedForTheCondition() {
        for (ItemAssessment item : pointsOfTheInnerLine()) {
            ItemAssessment.Attempt.Searched no = assertInstanceOf(
                    ItemAssessment.Attempt.Searched.class,
                    ((ItemAssessment.Owed) item).searches().only());
            assertTrue(no.way().takenIn().stream().allMatch(each ->
                            each.demand() instanceof RowDemand.ForTheRun(var _, var why, var _)
                                    && why == RowDemand.NoComposer.A_VALUE_THE_BODY_WORKS_OUT),
                    "the condition is a value the body works out: " + no.way().onTheWay());
            assertTrue(no.uncomposed().onTheWay().stream().anyMatch(each ->
                            each instanceof ReachabilityGap.Uncomposed(var _,
                                    ReachabilityGap.Why.NoComposerWritesIt(var what, var _))
                                    && what == RowDemand.NoComposer.A_VALUE_THE_BODY_WORKS_OUT),
                    "and the composer says it wrote nothing for it: " + no.uncomposed());
        }
    }

    /**
     * The word the one search of a point came back with.
     *
     * <p>Asked of the outcome rather than of which outcome it is. A point is put one value after
     * another until the figure for how many ends the asking, so the word a search that reached no
     * row came back with arrives wearing that figure as often as not — and it is the same word
     * either way.
     */
    private static Generator.UnresolvedCombination.Reason wordOf(ItemAssessment.Owed owed) {
        return switch (owed.searches().only()) {
            case ItemAssessment.Attempt.Unresolved it -> it.why().reason();
            case ItemAssessment.Attempt.Limited it -> it.why().reason();
            default -> null;
        };
    }

    /** And every row that is offered settles what it was composed for, which is what the first half
     *  costing rows buys. */
    @Test
    void everyRowThatIsOfferedSettlesWhatItWasComposedFor() {
        Settlements table = settlements();
        assertFalse(table.composedFor().isEmpty(), "rows are composed for this model");
        table.composedFor().forEach((item, row) -> {
            Map<ObligationIdentity, Settlement> here = table.byRow().get(row);
            assertNotNull(here, "the row composed for " + item + " is one this offers: " + row);
            assertFalse(here.get(item) instanceof Settlement.DoesNotSettle,
                    "a row composed for " + item + " is not read as standing elsewhere: " + row);
        });
    }

    /** What was searched for at each point of the line behind the product. */
    private static List<ItemAssessment> pointsOfTheInnerLine() {
        Compilation compilation = analysed();
        List<BorderAssessment> edges = compilation.db()
                .ask(new Adequacy.BoundarySearch("example.unspoken", "f")).value();
        assertNotNull(edges, "the lines of this behavior were searched");
        List<ItemAssessment> out = new java.util.ArrayList<>();
        for (BorderAssessment each : edges) {
            if (each.border().origin().comparisonAt().isEmpty()
                    || !isAt(each.border().obligation().at(), BEHIND_THE_PRODUCT)) {
                continue;
            }
            for (PointRole role : PointRole.values()) {
                if (each.at(role) instanceof ItemAssessment.Owed) {
                    out.add(each.at(role));
                }
            }
        }
        return out;
    }

    /** Whether a line was drawn at {@code number} of whatever it is a line of. */
    private static boolean isAt(souther.compiler.partition.Level level, Count number) {
        return level instanceof souther.compiler.partition.Level.OnACarrier(_, var at)
                && at instanceof Count count && count.compareTo(number) == 0;
    }

    private static Settlements settlements() {
        Compilation compilation = analysed();
        Map<String, Adequacy.Filling> generated =
                Adequacy.generatedOf(compilation.db(), "example.unspoken");
        assertNotNull(generated, "the model under test compiles");
        return Settlements.of(compilation.db(), Composition.composed(
                OfferingRequest.overTheModule("example.unspoken"), generated,
                Adequacy.accountFor(compilation.db(), "example.unspoken",
                        new GenerationScope.Module())));
    }

    private static Compilation analysed() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }
}
