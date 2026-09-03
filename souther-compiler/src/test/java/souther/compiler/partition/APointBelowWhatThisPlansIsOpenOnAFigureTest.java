package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.EstablishmentGap;
import souther.compiler.query.ItemAssessment;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A point whose position is deeper than this compiler plans is left open on the figure that stopped
 * the planning, and not on the model.
 *
 * <p>The line here is one an author writes in a line: a comparison against a field of a record that
 * happens to be nested nine deep. What this compiler does with it is stop at
 * {@link CompositionBudget#DEPTH_A_CONSTRUCTION_PLAN_DESCENDS} — and everything below that was a
 * plan with no position for the field, a composing that ran against it anyway, and a report saying
 * nothing composes a row for the point. Which reads as the model admitting no row where the row is
 * a nine-deep record an author would write out without noticing.
 *
 * <p><b>What is held here is the whole way through and not the plan alone.</b> The plan saying it
 * stopped short is fixed where the plan is
 * ({@code APlanSaysWhereItStoppedShortOfWhatTheValueHasTest}); this is the other half — that the
 * saying arrives at the account a reader asks, in a shape that names both the figure and the word
 * the search itself came back with.
 */
class APointBelowWhatThisPlansIsOpenOnAFigureTest {

    /**
     * Nine steps from the parameter to the field the line is drawn on.
     *
     * <p>Nothing here is unusual but the nesting. The comparison is the plainest one there is, the
     * types have no rules, and a row for either point is a record an author writes by hand in one
     * line — which is what makes the answer this used to give the wrong one.
     */
    private static final String MODEL = """
            module example.deep

            data L8 = { v: Int }
            data L7 = { down: L8 }
            data L6 = { down: L7 }
            data L5 = { down: L6 }
            data L4 = { down: L5 }
            data L3 = { down: L4 }
            data L2 = { down: L3 }
            data L1 = { down: L2 }

            data Query = { down: L1 }

            data Yes
            data No
            data Verdict = Yes | No

            behavior deeperThanThisPlans : (q: Query) -> Verdict
            let deeperThanThisPlans (q) =
                if q.down.down.down.down.down.down.down.down.v >= 7 then Yes else No
            """;

    /**
     * The point says which figure it is open on.
     *
     * <p>Both halves are asserted because neither is the other. That an account has a figure is
     * what tells this from the model refusing a row; that the figure is this one is what tells a
     * reader what to raise.
     */
    @Test
    void aPointThePlanCouldNotReachIsOpenOnTheDepthThisPlansTo() {
        List<ItemAssessment.Attempt> made = searchesOf(PointRole.ON);

        assertEquals(1, made.size(), "the line has one point ON it, searched once: " + made);
        ItemAssessment.Attempt.Limited limited = assertInstanceOf(
                ItemAssessment.Attempt.Limited.class, made.get(0),
                "the plan stopped short of the position the line is drawn at, so what came back is"
                        + " an answer about less than the point had");
        assertEquals(List.of(CompositionBudget.DEPTH_A_CONSTRUCTION_PLAN_DESCENDS),
                assertInstanceOf(EstablishmentGap.Composition.class, limited.by())
                        .budgets().written(),
                "and it is open on how deep this plans, which is a figure somebody could raise");
    }

    /**
     * And the obligation stays in the count, undecided.
     *
     * <p>The whole of what the figure buys. A point nothing showed a row for goes out of the count
     * as one the model may simply have nothing at; a point this compiler declined to work on stays
     * in it, because what is unknown is this run and not the model.
     */
    @Test
    void theObligationStaysCountedRatherThanBeingTakenForTheModelsAnswer() {
        for (ItemAssessment.Attempt made : searchesOf(PointRole.ON)) {
            assertInstanceOf(ItemAssessment.Attempt.Prevented.class, made,
                    "a search this compiler stopped short is one the account reads as prevented,"
                            + " which is what keeps the point counted");
        }
    }

    /**
     * The search's own word survives beside the figure, and says which way the point got here.
     *
     * <p>The half a reader loses if this arm is read as {@link ItemAssessment.Attempt.Stopped}.
     * That word is the budgets' to say and is checked against them, and these budgets have none —
     * so the only way to carry a search's own answer beside a figure like this is for the two to be
     * independent, and this is what says they are.
     *
     * <p><b>And it is the only thing here that says which route was taken.</b> Two of them end at
     * this same arm carrying this same figure: a demand the plan could not reach, refused before
     * any search ran, and a search that ran against a short plan and came to nothing. That they
     * converge is the design — what a reader is owed is the same either way — so the word is what
     * tells them apart, and asserting it is what keeps this test about the first of the two.
     */
    @Test
    void theWordTheSearchCameBackWithIsNotReadOffTheFigure() {
        ItemAssessment.Attempt.Limited limited = assertInstanceOf(
                ItemAssessment.Attempt.Limited.class, searchesOf(PointRole.ON).get(0));

        assertEquals(Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE,
                limited.why().reason(),
                "the search said what it found, which is that nothing composed a row here");
        assertTrue(limited.by() instanceof EstablishmentGap.Composition,
                "and the figure is carried beside it rather than the word being taken off it");
    }

    /**
     * A point held back by two figures at once names both of them.
     *
     * <p>The parameter nests past what this plans and carries a line whose edge offered less than
     * it had, so two different things are in the way at one point: a plan short of the value's
     * positions, and values the edge never built. Neither stands for the other and raising one
     * leaves the other where it was, so a reader asking what would let this go further is owed both
     * — and an outcome that names one is an author raising a figure that changes nothing.
     */
    @Test
    void aPointTwoFiguresHeldBackNamesEachOfThem() {
        List<CompositionBudget> named = new ArrayList<>();
        for (BorderAssessment border : lines(BOTH, "both")) {
            if (border.at(PointRole.ON) instanceof ItemAssessment.Owed owed) {
                for (ItemAssessment.Attempt each : owed.searches().each()) {
                    if (each instanceof ItemAssessment.Attempt.Limited it) {
                        named.addAll(assertInstanceOf(EstablishmentGap.Composition.class, it.by())
                                .budgets().written());
                    }
                }
            }
        }

        assertEquals(List.of(CompositionBudget.DECOMPOSITIONS_OF_A_TOTAL_OFFERED,
                        CompositionBudget.DEPTH_A_CONSTRUCTION_PLAN_DESCENDS), named,
                "the plan stopped short and the edge held values back, and the point is open on"
                        + " each of them");
    }

    /**
     * A parameter that both nests past the figure and carries a line whose edge holds values back.
     *
     * <p>The total is one no shape this offers reaches, which is what leaves the edge naming a
     * figure of its own; the nesting beside it is what leaves the plan short. Nothing relates the
     * two, which is the point — they are two pieces of work and a reader is owed both.
     */
    private static final String BOTH = """
            module example.both

            data Awkward = Int
                invariant value >= 0
                invariant value <= 10
                invariant value /= 3
                invariant value /= 4
                invariant value /= 7

            data Two = { xs: List<Awkward> }
                invariant List.length(xs) == 2

            data L8 = { v: Int }
            data L7 = { down: L8 }
            data L6 = { down: L7 }
            data L5 = { down: L6 }
            data L4 = { down: L5 }
            data L3 = { down: L4 }
            data L2 = { down: L3 }
            data L1 = { down: L2 }

            data Query = { two: Two, down: L1 }

            data Yes
            data No
            data Verdict = Yes | No

            behavior both : (q: Query) -> Verdict
            let both (q) =
                if List.sum(List.map(x -> x.value, q.two.xs)) >= 7 then Yes else No
            """;

    /** Every search of the point in the role given, across the lines this behavior draws. */
    private static List<ItemAssessment.Attempt> searchesOf(PointRole role) {
        List<ItemAssessment.Attempt> out = new ArrayList<>();
        for (BorderAssessment border : lines(MODEL, "deeperThanThisPlans")) {
            if (border.at(role) instanceof ItemAssessment.Owed owed) {
                out.addAll(owed.searches().each());
            }
        }
        return out;
    }

    /** The lines a behavior draws, read from the module the source declares itself to be. */
    private static List<BorderAssessment> lines(String source, String behavior) {
        String module = source.lines().filter(each -> each.startsWith("module "))
                .map(each -> each.substring("module ".length()).trim())
                .findFirst().orElseThrow();
        Map<String, List<BorderAssessment>> read =
                Adequacy.readingsOf(measured(source).db(), module);
        assertNotNull(read, "the model under test compiles");
        List<BorderAssessment> lines = read.get(behavior);
        assertNotNull(lines, "the behavior was measured");
        return lines;
    }

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.diagnostics().values().stream()
                        .flatMap(List::stream)
                        .map(each -> each.diagnostic().code()).toList(),
                "the model under test compiles");
        return compilation;
    }
}
