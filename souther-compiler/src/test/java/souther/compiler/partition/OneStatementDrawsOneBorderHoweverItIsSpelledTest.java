package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.PartitionEvidence;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule written over a standard-library operation draws the line the same rule written in
 * arithmetic draws.
 *
 * <p>{@code Date.daysBetween(a, b) > 10} and {@code b > Date.addDays(10, a)} are one statement, and
 * both are {@code b - a > 10}. Neither drew a line: the reading had no rule for what such an
 * operation answers, so the comparison came back as one this compiler does not read — while the
 * same statement over {@code Int.subtract} was measured.
 *
 * <p>What closed it is one fact per operation, said where nothing reads it and composed by the
 * walk both readers share. So the operations below cost the partition no arm of its own, and an
 * operation the library declares tomorrow costs it none either.
 */
class OneStatementDrawsOneBorderHoweverItIsSpelledTest {

    /** {@code Date.daysBetween(a, b) > 10} draws the border, and at the value it names. */
    @Test
    void aComparisonOverAMeasureOfTwoDatesDrawsTheLineTheirDifferenceDraws() {
        assertEquals(List.of("b - 10"), bordersOf("a: Date, b: Date",
                "Date.daysBetween(a, b) > 10"));
    }

    /**
     * And the same statement spelled as a shift draws the same line, from the other end.
     *
     * <p>{@code b > Date.addDays(10, a)} says what {@code Date.daysBetween(a, b) > 10} says. The
     * borders name different positions because each is written beside a different one, which is
     * what a line between two positions is: one line, said from whichever end the rule named.
     */
    @Test
    void theSameStatementSpelledAsAShiftDrawsTheSameLine() {
        assertEquals(List.of("a + 10"), bordersOf("a: Date, b: Date",
                "b > Date.addDays(10, a)"));
    }

    /** Turned round, the border is at the other position. */
    @Test
    void theMeasureTheOtherWayRoundDrawsTheBorderTheOtherWayRound() {
        assertEquals(List.of("a - 10"), bordersOf("a: Date, b: Date",
                "Date.daysBetween(b, a) > 10"));
    }

    /**
     * Against a position rather than a written number, both spellings reach the form.
     *
     * <p>{@code b - a - n} over {@code DATE}, {@code DATE} and {@code WHOLE} — the form a quantity
     * could not be over until its terms carried their own orders. The level is nought because the
     * threshold has been moved into it, which is what a form quantity is.
     */
    @Test
    void aMeasureAgainstAPositionReachesTheFormBothWaysRound() {
        assertEquals(List.of("0"), bordersOf("a: Date, b: Date, n: Int",
                "Date.daysBetween(a, b) > n"));
        assertEquals(List.of("0"), bordersOf("a: Date, b: Date, n: Int",
                "b > Date.addDays(n, a)"));
    }

    /**
     * And what it answers is what the arithmetic spelling has always answered.
     *
     * <p>Asserted against {@code Int.subtract} rather than against a value written here, so that
     * the two cannot drift apart: the point is not that a date rule reaches some particular border
     * but that it reaches the one its arithmetic reaches.
     */
    @Test
    void aDateRuleIsMeasuredTheWayItsArithmeticSpellingIsMeasured() {
        assertEquals(bordersOf("a: Int, b: Int, n: Int", "Int.subtract(b, a) > n"),
                bordersOf("a: Date, b: Date, n: Int", "Date.daysBetween(a, b) > n"),
                "one statement, one quantity, whatever the operands are counted on");
        assertEquals(reasonsOf("a: Int, b: Int", "Int.subtract(b, a) > 10"),
                reasonsOf("a: Date, b: Date", "Date.daysBetween(a, b) > 10"),
                "and no partition either way: a line between two positions divides neither");
    }

    /**
     * An operation stating no such form is still what it was.
     *
     * <p>{@code DateTime.minutesBetween} counts whole minutes over an order counting seconds and
     * drops the remainder toward zero, so it is not the difference of two counts. The declaration
     * says there is nothing to say of it, and the report says the rule is about a value made from
     * the positions — which is what it is.
     */
    @Test
    void anOperationDeclaredToStateNoSuchFormIsStillARuleAboutADerivedValue() {
        assertEquals(List.of(), bordersOf("a: DateTime, b: DateTime",
                "DateTime.minutesBetween(a, b) > 10"));
        assertEquals(List.of(UndividedPosition.Reason.RULE_ABOUT_A_DERIVED_VALUE,
                        UndividedPosition.Reason.RULE_ABOUT_A_DERIVED_VALUE),
                reasonsOf("a: DateTime, b: DateTime", "DateTime.minutesBetween(a, b) > 10"));
    }

    /**
     * A component of a value is not a form of it, and is a line all the same.
     *
     * <p>The other way a rule reaches a position. A form says what a result is in the counts of what
     * it was given, so the rule is read into the arguments and the border falls where the arithmetic
     * puts it. A component is no such arithmetic — the months are of different lengths, so no step
     * over the day count answers the year — and the operation says instead which representation
     * reads the number it answers. Read that way, {@code Date.year(a) > 2020} is a border on what
     * {@code a} may be, and the position is divided.
     *
     * <p>Beside the case above and not folded into it. What {@code DateTime.minutesBetween} answers
     * is read by nothing at all, so the rule stays about a value made from the positions; the
     * difference between the two is which representation the operation declares, and it shows here
     * as a border against no border.
     */
    @Test
    void aComponentOfAValueIsABorderOnThePositionItIsTakenOf() {
        assertEquals(List.of("2020"), bordersOf("a: Date", "Date.year(a) > 2020"));
        assertEquals(List.of(), reasonsOf("a: Date", "Date.year(a) > 2020"));
    }

    /**
     * A shift over the seconds a date-time counts, which is the same fact at another unit.
     *
     * <p>Declared beside the dates because it is exact for the same reason: the value carries no
     * zone, so a day is eighty-six thousand four hundred seconds of it and nothing shifts that.
     */
    @Test
    void aShiftOfADateTimeIsMeasuredToo() {
        assertTrue(!bordersOf("a: DateTime, b: DateTime", "b > DateTime.addHours(2, a)").isEmpty(),
                "a rule over a shifted date-time draws a line");
    }

    /**
     * An exclusion inside the call stops the reading there, which is why the corpus did not move.
     *
     * <p>The conformance corpus writes {@code Date.daysBetween(受付日, DateTime.toDate(締切))}, and
     * its report is the same document as before. That is not because nothing was gained: the one
     * place it uses the measure has an operation inside it that is declared to state no form, so the
     * reading reaches the argument and stops. Written without it, the same rule draws a line.
     */
    @Test
    void anExclusionInsideTheCallStopsTheReadingThere() {
        assertEquals(List.of(), bordersOf("a: Date, d: DateTime",
                "Date.daysBetween(a, DateTime.toDate(d)) <= 1"));
        assertEquals(List.of("b - 1"), bordersOf("a: Date, b: Date",
                "Date.daysBetween(a, b) <= 1"));
    }

    private static PartitionEvidence measured(String parameters, String condition) {
        String model = """
                module demo

                data Ok
                data No

                behavior f : (%s) -> Ok | No
                let f (%s) = {
                    guard %s else No
                    Ok
                }
                """.formatted(parameters,
                parameters.replaceAll(":\\s*[A-Za-z<>]+", ""), condition);
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, PartitionEvidence> coverage =
                compilation.db().ask(new Adequacy.Coverage("demo")).value();
        assertNotNull(coverage, () -> "the model under test compiles: " + model);
        PartitionEvidence measured = coverage.get("f");
        assertNotNull(measured, () -> "f was measured: " + model);
        return measured;
    }

    private static List<String> bordersOf(String parameters, String condition) {
        return measured(parameters, condition).boundaries().stream()
                .map(BorderAssessment::value).toList();
    }

    private static List<UndividedPosition.Reason> reasonsOf(String parameters, String condition) {
        return measured(parameters, condition).notRead().stream()
                .map(PartitionEvidence.NotRead::reason).toList();
    }
}
