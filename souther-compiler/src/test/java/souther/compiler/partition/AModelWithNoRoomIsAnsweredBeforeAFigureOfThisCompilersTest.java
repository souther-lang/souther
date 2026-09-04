package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A collection the rules leave no room in is answered as that, and not as a figure this compiler
 * reached while finding out.
 *
 * <p>The two can be true of one point at once, and it is the ordinary case rather than a contrived
 * one: where the model has no row, the search refuses everything it composes and goes on composing
 * until it meets a bound. So which of the two a reader is told turns on nothing about the model,
 * and everything about which was asked first.
 *
 * <p><b>What settles it is that only one of them is actionable.</b> A proof that no collection
 * holds what is being placed in it stands however far this compiler read; an author sent to raise
 * the figure beside it would raise it and be told the same thing. So the proof is made where the
 * plan is, before any search runs, and the search that would have named a figure never happens.
 *
 * <p>The pair below is the same rule read against two states of the row. Where the cap's own field
 * is settled at nought, the rules leave no room and the plan refuses; where it is settled at one,
 * they leave room for exactly what is placed, and a row is written. The proof is not a property of
 * the rule but of the rule and what the row has fixed.
 */
class AModelWithNoRoomIsAnsweredBeforeAFigureOfThisCompilersTest {

    /**
     * A list capped at a field beside it, asked for with a value inside it.
     *
     * <p>The line asks both at once, so a combination fixes {@code cap} and asks for a class at an
     * element of {@code xs}. Where it fixes {@code cap} at nought the two cannot both hold: the
     * rules cap the list at none, and what is asked for is a list holding one.
     *
     * <p>The fields beside them are what make the search wide enough to meet its bound. They relate
     * to nothing here and are refused for nothing of their own, which is the point — the figure a
     * reader would be sent to raise has nothing to do with why no row exists.
     */
    private static final String CAPPED = """
            module example.placing

            data Awkward = Int
                invariant lo = value >= 0
                invariant hi = value <= 10
                invariant no3 = value /= 3
                invariant no4 = value /= 4
                invariant no7 = value /= 7

            data Box =
                { cap: Int
                , xs: List<Awkward>
                , a: Awkward
                , b: Awkward
                , c: Awkward
                , d: Awkward
                , e: Awkward
                , f: Awkward
                , g: Awkward
                , h: Awkward
                , i: Awkward
                , j: Awkward
                , k: Awkward
                , l: Awkward
                }
                invariant floor = cap >= 0
                invariant capped = List.length(xs) <= cap

            data Yes
            data No
            data Verdict = Yes | No

            behavior placing : (box: Box) -> Verdict
            let placing (box) =
                if box.cap >= 1 && List.length(List.filter(x -> x.value >= 5, box.xs)) >= 1
                then Yes
                else No
            """;

    /**
     * The combination the rules leave no room for is answered by the model, and by nothing else.
     *
     * <p>Both halves. That the word is the model's is what sends an author somewhere they can act;
     * that no figure of this compiler's is named is what keeps them from raising one that changes
     * nothing. Before the refusal was made where the plan is, this combination came back saying the
     * search had left something untried — which was true and was not what a reader needed.
     */
    @Test
    void theCombinationWithNoRoomIsAnsweredByTheModel() {
        List<Generator.UnresolvedCombination> made = unresolved();

        assertFalse(made.isEmpty(), "the combination is one no row was written for");
        for (Generator.UnresolvedCombination each : made) {
            assertEquals(Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE,
                    each.reason(),
                    () -> "the model settles it, whatever the search then did: " + each);
        }
    }

    /** And every one of them says which collection, how many it needs, and how many it may hold. */
    @Test
    void theAnswerSaysWhatTheRulesLeaveRoomFor() {
        for (Generator.UnresolvedCombination each : unresolved()) {
            String said = each.detail();

            assertNotNull(said, () -> "the answer says what it is about: " + each);
            assertTrue(said.contains("box.xs") && said.contains("hold 1")
                            && said.contains("room for 0"),
                    () -> "and says the collection, what it would have to hold, and what the rules"
                            + " leave room for: " + said);
        }
    }

    /**
     * A search that met a figure of this compiler's still says so.
     *
     * <p>The control against reading too much into the rules. Where the row has not fixed the cap
     * the rules leave the list holding whatever a larger one would allow, nothing is proved, and
     * what this compiler has to say is what it did. A refusal made from the cap alone rather than
     * from the cap the row fixed would take these with it and leave the figure unreachable.
     *
     * <p>Asked of every search the account holds and not of a chosen few. Which of them are about
     * a position inside the list is a question the account does not answer, and picking them out of
     * how a class is spelled is how a reading of this model came to be about the wrong ones.
     */
    @Test
    void aSearchThatMetTheFigureStillSaysSo() {
        assertTrue(everySearch().stream()
                        .anyMatch(each -> each instanceof ItemAssessment.Attempt.Stopped stopped
                                && stopped.stoppedBy().written()
                                        .contains(CompositionBudget.ASSIGNMENTS_A_SEARCH_COMPOSES)),
                "a search of this behavior meets the assignments a search composes: "
                        + everySearch());
    }

    /**
     * And the same rule leaves the rows it has room for.
     *
     * <p>The other control. What is refused above turns on the cap the row fixed and not on the
     * rule alone, so a cap of one leaves a list holding one.
     */
    @Test
    void theSameRuleLeavesTheRowsItHasRoomFor() {
        assertTrue(rowsOf("placing").stream()
                        .anyMatch(each -> each.contains("cap = 1") && !each.contains("xs = []")),
                "a row holding one under a cap of one is written: " + rowsOf("placing"));
    }

    /** The combinations no row was written for, as the filling records them. */
    private static List<Generator.UnresolvedCombination> unresolved() {
        Adequacy.Filling filling = measured().db()
                .ask(new Adequacy.Generated("example.placing", "placing")).value();
        assertNotNull(filling, "rows are asked for");
        return filling.composed().unresolved();
    }

    /** Every search this behavior's account holds, whatever point or role it was for. */
    private static List<ItemAssessment.Attempt> everySearch() {
        List<ItemAssessment.Attempt> out = new ArrayList<>();
        for (BorderAssessment border : lines("placing")) {
            for (PointRole role : PointRole.values()) {
                if (border.at(role) instanceof ItemAssessment.Owed owed) {
                    out.addAll(owed.searches().each());
                }
            }
        }
        return out;
    }

    /** The rows the behavior was offered, as they are written out. */
    private static List<String> rowsOf(String behavior) {
        Adequacy.Filling filling = measured().db()
                .ask(new Adequacy.Generated("example.placing", behavior)).value();
        assertNotNull(filling, "rows are asked for");
        return filling.composed().rows().stream()
                .map(row -> row.inputs().get(0).text()).toList();
    }

    /** The lines a behavior draws. */
    private static List<BorderAssessment> lines(String behavior) {
        Map<String, List<BorderAssessment>> read =
                Adequacy.readingsOf(measured().db(), "example.placing");
        assertNotNull(read, "the model under test compiles");
        List<BorderAssessment> lines = read.get(behavior);
        assertNotNull(lines, "the behavior was measured");
        return lines;
    }

    private static Compilation measured() {
        Compilation compilation = Compilation.ofSource(CAPPED, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.diagnostics().values().stream()
                        .flatMap(List::stream)
                        .map(each -> each.diagnostic().code()).toList(),
                "the model under test compiles");
        return compilation;
    }
}
