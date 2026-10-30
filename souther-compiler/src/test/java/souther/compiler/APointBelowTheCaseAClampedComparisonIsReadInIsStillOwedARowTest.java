package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison on a clamped quantity draws its line in the case of the clamp where it does not
 * clamp, and the classes that line cuts run over the whole of the quantity.
 *
 * <p>{@code List.length(List.drop(1, xs)) >= 1} turns at {@code List.length(xs) == 2}, and the
 * line is read in the case {@code List.length(xs) >= 1}. The class below the line,
 * {@code xs == []}, lies wholly outside that case and is still a place the comparison is reached
 * with a value and answers: it is owed a row, and a row of it is one whose run had the comparison
 * come out as the class says, whether an author wrote it or a search composed it.
 */
class APointBelowTheCaseAClampedComparisonIsReadInIsStillOwedARowTest {

    private static final String DROPPED = "List.length(List.drop(1, xs)) >= 1";

    private static final String REFUTED_OUT = "no row can stand at the OUT point";

    private static final String THE_OUT_CLASS = "in 0 <= List.length(xs) < 1";

    private static String modelComparing(String condition) {
        return """
                module p
                data Yes
                data No
                behavior f : (xs: List<Int>) -> Yes | No
                let f (xs) = if CONDITION then Yes else No
                """.replace("CONDITION", condition);
    }

    private static String report(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        assertTrue(compilation.errors().isEmpty(), () -> "the model compiles: " + compilation.errors());
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    /** The border is drawn on the length, at 2, and its OUT class is owed and not refuted. */
    @Test
    void theOutClassOfALengthAfterADropIsOwedAndNotRefuted() {
        String human = report(modelComparing(DROPPED));

        assertTrue(human.contains("read as f/List.length(xs): = 2"), human);
        assertTrue(human.contains(THE_OUT_CLASS), human);
        assertFalse(human.contains(REFUTED_OUT), human);
        assertFalse(human.contains("no value can stand at 0 <= List.length(xs) < 1"), human);
    }

    @Test
    void theSameComparisonAsStrictlyMoreThanNoughtIsOwedTheSame() {
        String human = report(modelComparing("List.length(List.drop(1, xs)) > 0"));

        assertTrue(human.contains(THE_OUT_CLASS), human);
        assertFalse(human.contains(REFUTED_OUT), human);
    }

    @Test
    void theSameComparisonAsNotEmptyIsOwedTheSame() {
        String human = report(modelComparing("Bool.not(List.isEmpty(List.drop(1, xs)))"));

        assertTrue(human.contains(THE_OUT_CLASS), human);
        assertFalse(human.contains(REFUTED_OUT), human);
    }

    /** The search composes a row for the class, reads it back and has it certified. */
    @Test
    void aRowCanBeWrittenAtTheClass() {
        String human = report(modelComparing(DROPPED));

        assertFalse(human.contains("nothing could show a row can be written at the OUT point"),
                human);
    }

    /** A row an author wrote is a row of the class as a composed one is. */
    @Test
    void aWrittenRowOfAnEmptyListMeetsTheOutClass() {
        String human = report(modelComparing(DROPPED) + """
                example f
                    | "empty" : ([]) -> No
                """);

        assertTrue(human.contains("obligations 1/4"), human);
        assertFalse(human.contains("no row is at an OUT point"), human);
        assertTrue(human.contains("no row is at the ON point"), human);
    }

    /**
     * A row in the class of the quantity the comparison comes out the other way for is no row of
     * the class: three elements put the length in the class above the line, where it holds.
     */
    @Test
    void aWrittenRowTheComparisonHoldsForIsNotAtTheOutClass() {
        String human = report(modelComparing(DROPPED) + """
                example f
                    | "three" : ([1, 2, 3]) -> Yes
                """);

        assertTrue(human.contains("no row is at an OUT point"), human);
    }

    /**
     * The case the line is read in is a condition on another input, and the quantity stands
     * whatever that input is: the class is owed, not refuted.
     */
    @Test
    void aCaseOnAnotherInputDoesNotMakeTheClassOneNoValueStandsAt() {
        String human = report("""
                module p
                data Yes
                data No
                behavior f : (xs: List<Int>, enabled: Bool) -> Yes | No
                let f (xs, enabled) =
                    if (if enabled then List.length(List.drop(1, xs)) else 0) >= 1
                    then Yes else No
                """);

        assertTrue(human.contains(THE_OUT_CLASS), human);
        assertFalse(human.contains(REFUTED_OUT), human);
    }

    /** A declaration that leaves no empty list is a reason the rules give, and it still refutes. */
    @Test
    void aClassTheDeclarationsLeaveNoValueAtIsStillExcluded() {
        String human = report("""
                module p
                data Yes
                data No
                data Xs = { items: List<Int> }
                    invariant nonEmpty = List.length(items) >= 1
                behavior f : (xs: Xs) -> Yes | No
                let f (xs) = if List.length(List.drop(1, xs.items)) >= 1 then Yes else No
                """);

        assertTrue(human.contains("no OUT point is owed at List.length(xs.items) = 2"), human);
        assertFalse(human.contains(THE_OUT_CLASS), human);
    }

    /** A guard that turns an empty list back before the comparison leaves no run to the class. */
    @Test
    void aClassAGuardBeforeTheComparisonTurnsBackIsStillExcluded() {
        String human = report("""
                module p
                data Yes
                data No
                behavior f : (xs: List<Int>) -> Yes | No
                let f (xs) =
                    if List.length(xs) >= 1
                    then if List.length(List.drop(1, xs)) >= 1 then Yes else No
                    else No
                """);

        assertTrue(human.contains("no OUT point is owed at List.length(xs) = 2"), human);
    }
}
