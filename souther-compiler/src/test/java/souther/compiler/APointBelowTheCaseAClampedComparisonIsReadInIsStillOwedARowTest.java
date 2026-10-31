package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;
import souther.compiler.query.Measurement;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
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

    /** The search composes a row for the class, reads it back, and has it certified: the empty list. */
    @Test
    void theSearchComposesTheEmptyListAndReadsItBackAtTheOutClass() {
        List<ItemAssessment.Owed> out = owedPointsBelowTheLine(modelComparing(DROPPED));

        assertEquals(1, out.size(), () -> "the OUT class is one owed point: " + out);
        List<List<String>> certified = out.getFirst().searches().each().stream()
                .filter(ItemAssessment.Attempt.Certified.class::isInstance)
                .map(ItemAssessment.Attempt.Certified.class::cast)
                .map(row -> row.row().inputs().stream().map(input -> input.text()).toList())
                .toList();
        assertEquals(List.of(List.of("[]")), certified, () -> "searches: " + out.getFirst());
    }

    private static List<ItemAssessment.Owed> owedPointsBelowTheLine(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, List<BorderAssessment>> all =
                Adequacy.readingsOf(compilation.db(), compilation.modules().get(0));
        assertNotNull(all, () -> "the model compiles: " + compilation.errors());
        return BorderAssessment.pointsOf(all.get("f")).stream()
                .filter(point -> point.label() != null && point.label().contains("< 1"))
                .map(BorderAssessment.Point::item)
                .filter(ItemAssessment.Owed.class::isInstance)
                .map(ItemAssessment.Owed.class::cast)
                .toList();
    }

    /**
     * One comparison read in two cases, the clamp in one and the length as it is in the other. A row
     * of the case that has its own line is a row of that line's classes, and is no row of a class
     * the other reading cuts although the number is in it and the comparison comes out the same way.
     */
    private static final String PER_TERM = """
            module p
            data Term = OneYear | TwoYear
            data Yes
            data No
            behavior f : (term: Term, xs: List<Int>) -> Yes | No
            let f (term, xs) =
                if (match term with
                        | OneYear -> List.length(List.drop(1, xs))
                        | TwoYear -> List.length(xs)) >= 1
                then Yes else No
            """;

    private static ItemAssessment.Owed theOneYearOutClass(String source) {
        List<ItemAssessment.Owed> out = owedPointsBelowTheLine(source);
        assertEquals(1, out.size(), () -> "one owed point below the one-year line: " + out);
        return out.getFirst();
    }

    @Test
    void theOneYearOutClassIsComposedWithAOneYearRow() {
        ItemAssessment.Owed owed = theOneYearOutClass(PER_TERM);

        List<List<String>> certified = owed.searches().each().stream()
                .filter(ItemAssessment.Attempt.Certified.class::isInstance)
                .map(ItemAssessment.Attempt.Certified.class::cast)
                .map(row -> row.row().inputs().stream().map(input -> input.text()).toList())
                .toList();
        assertEquals(List.of(List.of("OneYear", "[]")), certified, () -> "searches: " + owed);
    }

    @Test
    void aWrittenRowOfTheOtherTermIsNoRowOfTheOneYearOutClass() {
        ItemAssessment.Owed owed = theOneYearOutClass(PER_TERM + """
                example f
                    | "two empty" : (TwoYear, []) -> No
                """);

        assertTrue(owed.coverage().made().filter(ItemAssessment.Coverage.NoHit.class::isInstance)
                .isPresent(), () -> "a two-year row is no row of the one-year class: " + owed);
    }

    @Test
    void aWrittenRowOfTheOneYearTermIsARowOfItsOutClass() {
        ItemAssessment.Owed owed = theOneYearOutClass(PER_TERM + """
                example f
                    | "one empty" : (OneYear, []) -> No
                """);

        assertTrue(owed.coverage().made().filter(ItemAssessment.Coverage.Hit.class::isInstance)
                .isPresent(), () -> "a one-year row is a row of the one-year class: " + owed);
    }

    /**
     * One comparison with a line on each of two positions. The empty list is in the clamped line's
     * class, and it is also in the case the line on the other position decides in, so it is a row of
     * that reading. Written by an author or composed by a search, the same row gets the same answer.
     */
    private static final String TWO_POSITIONS = """
            module p
            data Yes
            data No
            behavior f : (xs: List<Int>, ys: List<Int>) -> Yes | No
            let f (xs, ys) =
                if Int.max(List.length(List.drop(1, xs)), List.length(ys)) >= 1
                then Yes else No
            """;

    @Test
    void aRowInTheCaseOfALineOnAnotherPositionIsNoRowOfTheClassWhoeverMadeIt() {
        ItemAssessment.Owed written = theOutClassOf(TWO_POSITIONS + """
                example f
                    | "both empty" : ([], []) -> No
                """, "xs");
        assertTrue(written.coverage().made().filter(ItemAssessment.Coverage.NoHit.class::isInstance)
                .isPresent(), () -> "a written row of the other reading is no hit: " + written);
        assertTrue(written.searches().each().stream()
                .noneMatch(ItemAssessment.Attempt.Certified.class::isInstance),
                () -> "nor is a composed one certified: " + written);
    }

    private static ItemAssessment.Owed theOutClassOf(String source, String position) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, List<BorderAssessment>> all =
                Adequacy.readingsOf(compilation.db(), compilation.modules().get(0));
        assertNotNull(all, () -> "the model compiles: " + compilation.errors());
        List<ItemAssessment.Owed> found = BorderAssessment.pointsOf(all.get("f")).stream()
                .filter(point -> point.label() != null
                        && point.label().contains("0 <= List.length(" + position + ") < 1"))
                .map(BorderAssessment.Point::item)
                .filter(ItemAssessment.Owed.class::isInstance)
                .map(ItemAssessment.Owed.class::cast)
                .toList();
        assertEquals(1, found.size(), () -> "one OUT class on " + position + ": " + found);
        return found.getFirst();
    }

    /**
     * A comparison made once for each element of a list. The run's record is of the place and not of
     * the element a reading chose, and here the answers disagree: which belongs to the element is
     * not told, and that is said as a measurement that could not look and not as a row that is not
     * at the class.
     */
    @Test
    void anApplicationNotToldApartFromTheOthersIsNotARowThatMissesTheClass() {
        ItemAssessment.Owed owed = theOutClassOfEachElement("""
                module p
                data Yes
                data No
                behavior f : (xss: List<List<Int>>) -> Yes | No
                let f (xss) =
                    if List.any(xs -> List.length(List.drop(1, xs)) >= 1, xss)
                    then Yes else No
                example f
                    | "mixed" : ([[], [1, 2]]) -> Yes
                """);

        assertInstanceOf(Measurement.Partial.class, owed.coverage(),
                () -> "the row could not be told apart, which is not a complete miss: " + owed);
    }

    private static ItemAssessment.Owed theOutClassOfEachElement(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, List<BorderAssessment>> all =
                Adequacy.readingsOf(compilation.db(), compilation.modules().get(0));
        assertNotNull(all, () -> "the model compiles: " + compilation.errors());
        List<ItemAssessment.Owed> found = BorderAssessment.pointsOf(all.get("f")).stream()
                .filter(point -> point.label() != null
                        && point.label().contains("0 <= List.length(xss[*]) < 1"))
                .map(BorderAssessment.Point::item)
                .filter(ItemAssessment.Owed.class::isInstance)
                .map(ItemAssessment.Owed.class::cast)
                .toList();
        assertEquals(1, found.size(), () -> "one OUT class on the elements: " + found);
        return found.getFirst();
    }

    /** The comparison inside a conjunction is read as it is alone: the class is owed. */
    @Test
    void aComparisonInAConjunctionHasTheSameOwedClassAndAWrittenRowMeetsIt() {
        String source = """
                module p
                data Yes
                data No
                behavior f : (xs: List<Int>, enabled: Bool) -> Yes | No
                let f (xs, enabled) =
                    if List.length(List.drop(1, xs)) >= 1 && enabled then Yes else No
                example f
                    | "empty" : ([], true) -> No
                """;
        String human = report(source);

        assertTrue(human.contains("obligations 1/4"), human);
        assertFalse(human.contains(REFUTED_OUT), human);
        assertFalse(human.contains("no row is at an OUT point"), human);
    }

    /** A negated comparison: the rule's holding is the comparison's not holding. */
    @Test
    void aNegatedComparisonIsReadByTheSideTheRuleHoldsOn() {
        String source = """
                module p
                data Yes
                data No
                behavior f : (xs: List<Int>) -> Yes | No
                let f (xs) = if Bool.not(List.length(List.drop(1, xs)) < 1) then Yes else No
                example f
                    | "empty" : ([]) -> No
                    | "three" : ([1, 2, 3]) -> Yes
                """;
        String human = report(source);

        assertFalse(human.contains(REFUTED_OUT), human);
        assertFalse(human.contains("no row is at an OUT point"), human);
        assertFalse(human.contains("no row is at an IN point"), human);
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
