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
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
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

    /** And the answer says which collection, how many it would have to hold, and how many it may. */
    @Test
    void theAnswerSaysWhatTheRulesLeaveRoomFor() {
        String said = unresolved().getFirst().detail();

        assertNotNull(said, "the answer says what it is about: " + unresolved());
        assertTrue(said.contains("box.xs") && said.contains("hold 1") && said.contains("room for 0"),
                "and says the collection, what it would have to hold, and what the rules leave"
                        + " room for: " + said);
    }

    /**
     * A point whose cap the row has not fixed is left open on the figure the search reached.
     *
     * <p>The control against reading too much into the rules. Nothing here settles {@code cap}, so
     * the rules leave the list holding whatever a larger one would allow and no refusal is proved —
     * and what this compiler has to say is what it did. A refusal made from the cap alone would
     * take these with it.
     */
    @Test
    void aPointTheRowHasNotFixedTheCapAtStaysOpenOnTheFigure() {
        List<ItemAssessment.Attempt> made = insideTheList("placing");

        assertFalse(made.isEmpty(), "the classes of the element are asked about");
        for (ItemAssessment.Attempt each : made) {
            ItemAssessment.Attempt.Stopped stopped = assertInstanceOf(
                    ItemAssessment.Attempt.Stopped.class, each,
                    () -> "the search met a figure and says so: " + each);
            assertEquals(List.of(CompositionBudget.ASSIGNMENTS_A_SEARCH_COMPOSES),
                    stopped.stoppedBy().written(),
                    "and names the figure rather than a refusal it has not proved");
        }
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

    /**
     * Every search of a point standing inside the capped list, asked with nothing on the way to it.
     *
     * <p>Those asked under a condition on {@code cap} are a different question: the way already
     * says what the row has to be. What is left is the points the combination itself fixes the cap
     * at, which is where a reading of the rules is all there is to go on.
     */
    private static List<ItemAssessment.Attempt> insideTheList(String behavior) {
        List<ItemAssessment.Attempt> out = new ArrayList<>();
        for (BorderAssessment border : lines(behavior)) {
            for (PointRole role : PointRole.values()) {
                if (border.at(role) instanceof ItemAssessment.Owed owed) {
                    owed.searches().each().stream()
                            .filter(each -> about(each).contains("xs["))
                            .filter(each -> wayTo(each).onTheWay().isEmpty())
                            .forEach(out::add);
                }
            }
        }
        return out;
    }

    /** What a search was about, in the words the account names its classes by. */
    private static String about(ItemAssessment.Attempt made) {
        return switch (made) {
            case ItemAssessment.Attempt.Certified it -> it.row().purposes().toString();
            case ItemAssessment.Attempt.Unverified it -> it.row().purposes().toString();
            case ItemAssessment.Attempt.Stopped it -> it.why().classes().toString();
            case ItemAssessment.Attempt.Unexhausted it -> it.why().classes().toString();
            case ItemAssessment.Attempt.Limited it -> it.why().classes().toString();
            case ItemAssessment.Attempt.Unplanned it -> it.why().classes().toString();
            case ItemAssessment.Attempt.Unresolved it -> it.why().classes().toString();
            case ItemAssessment.Attempt.Unavailable it -> it.toString();
        };
    }

    /** What had to hold on the way to the point the search was for. */
    private static WayToTheBorder wayTo(ItemAssessment.Attempt made) {
        return switch (made) {
            case ItemAssessment.Attempt.Certified it -> it.way();
            case ItemAssessment.Attempt.Unverified it -> it.way();
            case ItemAssessment.Attempt.Stopped it -> it.way();
            case ItemAssessment.Attempt.Unexhausted it -> it.way();
            case ItemAssessment.Attempt.Limited it -> it.way();
            case ItemAssessment.Attempt.Unplanned it -> it.way();
            case ItemAssessment.Attempt.Unresolved it -> it.way();
            case ItemAssessment.Attempt.Unavailable _ -> new WayToTheBorder(List.of());
        };
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
