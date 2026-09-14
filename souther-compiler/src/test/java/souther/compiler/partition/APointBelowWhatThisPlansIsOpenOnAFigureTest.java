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
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

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

        assertEquals(1, made.size(), "the line has one point ON it, asked about once: " + made);
        ItemAssessment.Attempt.Unplanned unplanned = assertInstanceOf(
                ItemAssessment.Attempt.Unplanned.class, made.get(0),
                "the position the line is drawn at is under what this plans, so no value was"
                        + " planned and no search was made");
        assertEquals(List.of(CompositionBudget.DEPTH_A_CONSTRUCTION_PLAN_DESCENDS),
                assertInstanceOf(EstablishmentGap.Composition.class, unplanned.by())
                        .budgets().written(),
                "and it is open on how deep this plans, which is a figure somebody could raise");
    }

    /**
     * And nothing counts it as a search that ran.
     *
     * <p><b>The half that a shared arm would have thrown away.</b> What a point comes to and what
     * this run actually did are two facts, and they part here: the account's question — is the
     * point open on a figure — is answered the same as for a search a figure stopped, while the
     * history is that no search was made. Held as one outcome with the other, the reading would be
     * counted among the ones that were walked, and a line's readings together would rest on one
     * nobody looked at.
     */
    @Test
    void aPointNothingWasPlannedForIsNotCountedAsASearchThatRan() {
        ItemAssessment.Attempt made = searchesOf(PointRole.ON).get(0);

        assertFalse(made instanceof ItemAssessment.Attempt.Searched,
                "no search ran for it, so it is not an outcome of one");
        assertInstanceOf(ItemAssessment.Attempt.Prevented.class, made,
                "and the account still reads it as this compiler's own limit, which is what keeps"
                        + " the point counted");
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
     * A plan short of the value, where the search did run, is the other arm — and its word is its
     * own.
     *
     * <p>The line here is not below the figure, so the value is planned and searched; what the
     * search is handed is short, because the parameter nests past what this plans elsewhere. So
     * the answer is the search's own — every candidate refused — and the figure says that answer
     * is about less than the point had. The word is not read off the budgets: these budgets stop no
     * search and asking them for a word is what refuses to answer.
     *
     * <p>Which is the whole of what tells this from the point above. There the plan was never
     * made; here it was made, used, and short.
     */
    @Test
    void aSearchOverAShortPlanIsAnOutcomeOfASearchAndKeepsItsOwnWord() {
        ItemAssessment.Attempt.Limited limited = assertInstanceOf(
                ItemAssessment.Attempt.Limited.class, onlyPreventedOf(ONLY_DEPTH, "only"));

        assertInstanceOf(ItemAssessment.Attempt.Searched.class, limited,
                "the search ran over the plan it was handed, so it is an outcome of one");
        assertEquals(Generator.UnresolvedCombination.Reason.ALL_CANDIDATES_REJECTED,
                limited.why().reason(),
                "and it says what it found rather than what a figure would have said for it");
        assertEquals(List.of(CompositionBudget.DEPTH_A_CONSTRUCTION_PLAN_DESCENDS),
                assertInstanceOf(EstablishmentGap.Composition.class, limited.by())
                        .budgets().written(),
                "and the figure beside it is the one that left the plan short, alone");
    }

    /**
     * A rule that reaches a position deeper than this plans, on a point that is not itself deep.
     *
     * <p>The line is drawn on a plain field, so the value is planned and the search runs. What it
     * cannot satisfy is a rule of the record's own, which names a position the plan never reached —
     * so every row it builds is refused, and the reason it was never going to build one is that the
     * plan stopped short. Nothing else here holds anything back.
     *
     * <p>Which is the shape an author meets without noticing: the rule is one line, and how deeply
     * the record happens to nest is not something the rule says anything about.
     */
    private static final String ONLY_DEPTH = """
            module example.only

            data L8 = { v: Int }
            data L7 = { down: L8 }
            data L6 = { down: L7 }
            data L5 = { down: L6 }
            data L4 = { down: L5 }
            data L3 = { down: L4 }
            data L2 = { down: L3 }
            data L1 = { down: L2 }

            data Query = { down: L1, n: Int }
                invariant tied = n == down.down.down.down.down.down.down.down.v

            data Yes
            data No
            data Verdict = Yes | No

            behavior only : (q: Query) -> Verdict
            let only (q) = if q.n >= 7 then Yes else No
            """;

    /**
     * While an offer is still holding values, the plan being short says nothing yet.
     *
     * <p><b>A search that was not given everything it had has exhausted nothing.</b> Raise the
     * offer's figure and it may compose a row without the plan changing at all — so naming the
     * plan's figure here sends an author to raise one that would change nothing, and names it
     * beside a figure that is genuinely in the way, where the two look alike.
     *
     * <p>The plan is short in this model all the same, and that is what makes it worth asserting:
     * what stays quiet is a fact the plan is carrying, not a fact nobody has.
     */
    @Test
    void anOfferStillHoldingValuesLeavesThePlansFigureUnsaid() {
        ItemAssessment.Attempt.Unexhausted some = assertInstanceOf(
                ItemAssessment.Attempt.Unexhausted.class, onlyPreventedOf(BOTH, "both"),
                "the edge offered less than there is, which is a search that never had the whole of"
                        + " what there was to try — and not one a figure stopped");
        EstablishmentGap.Composition why = assertInstanceOf(
                EstablishmentGap.Composition.class, some.by());

        assertEquals(List.of(CompositionRepertoire.WAYS_A_TOTAL_IS_SPREAD),
                why.repertoires().written(),
                "so the point is open on what the edge writes some of, and the plan's own figure"
                        + " waits until there is nothing left to offer");
        assertEquals(List.of(), why.budgets().written(),
                "and no figure is named, because none refused anything: a reader told to raise one"
                        + " would raise it and get the same offer back");
    }

    /** The one search of this behavior the account reads as this compiler's own limit. */
    private static ItemAssessment.Attempt onlyPreventedOf(String source, String behavior) {
        List<ItemAssessment.Attempt> found = new ArrayList<>();
        for (BorderAssessment border : lines(source, behavior)) {
            if (border.at(PointRole.ON) instanceof ItemAssessment.Owed owed) {
                owed.searches().each().stream()
                        .filter(each -> each instanceof ItemAssessment.Attempt.Prevented)
                        .forEach(found::add);
            }
        }
        assertEquals(1, found.size(),
                "one point of this behavior is open on a figure of this compiler's: " + found);
        return found.get(0);
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
