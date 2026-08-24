package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.check.ComparisonClaim;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.NumericDomain.LinearForm;

import java.math.BigDecimal;
import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What one comparison divides, and where — asked of the comparison rather than of its shape.
 *
 * <p>A reading that answers "which variant of quantity is this" answers a different question from
 * "what does this rule divide". {@code n > 10} arrives as one position's own values and
 * {@code 2 * n > 40} as an arithmetic form over twice them, so the first divides the position into
 * classes and the second divides nothing — while the two rules part the same values in the same two
 * places. What a report counts, and what each rule's border knows about the lines beside it, both
 * follow from which of those two questions was asked.
 */
class ACutSaysWhatItDividesAndWhereTest {

    private static final Carrier WHOLE = new Carrier.Whole();

    private static NumericTerm term(String name) {
        return new NumericTerm.ValueOf(TermPath.of(name));
    }

    private static LinearForm<NumericTerm> form(String name, String coef) {
        Map<NumericTerm, BigDecimal> coefs = new LinkedHashMap<>();
        coefs.put(term(name), new BigDecimal(coef));
        return new LinearForm<>(BigDecimal.ZERO, coefs);
    }

    /** {@code n > t}, read as one position's own values. */
    private static Cutting onThePosition(String t) {
        return new Cutting(
                new BorderQuantity.OfACoordinate(AxisId.of("f", term("n")), term("n"), WHOLE),
                new Level.OnACarrier(WHOLE, new Count(new BigDecimal(t))),
                new ComparisonClaim.Cut(true, false), null);
    }

    /** {@code k * n > t}, read as an arithmetic form over a multiple of that position. */
    private static Cutting overAMultiple(String k, String t) {
        return new Cutting(
                new BorderQuantity.OverAForm("f", form("n", k), Map.of(term("n"), WHOLE)),
                new Level.ACount(new Count(new BigDecimal(t))),
                new ComparisonClaim.Cut(true, false), null);
    }

    /**
     * A rule written in twos cuts the position, not a form that divides nothing.
     *
     * <p>Which is what puts the second line back on {@code n}. Held apart, a position carrying both
     * rules is reported as having two equivalence partitions where the model states three, and the
     * class between twenty-one and the end of the order is one nothing counts.
     */
    @Test
    void aRuleWrittenInTwosCutsWhatARuleWrittenInOnesCuts() {
        assertEquals(onThePosition("10").quantity().key(), overAMultiple("2", "40").quantity().key(),
                "`n > 10` and `2 * n > 40` cut one quantity");
    }

    /** And it parts the values in the place the position's own numbers say, not the form's. */
    @Test
    void andPartsTheValuesWhereThePositionsOwnNumbersSayItDoes() {
        assertEquals("10|11", onThePosition("10").seam().key());
        assertEquals("20|21", overAMultiple("2", "40").seam().key(),
                "forty of a doubled position is twenty of it");
    }

    /**
     * A rule that singles a value out singles out a value, or none at all.
     *
     * <p>Two different questions, and one of them has been answering both. Where a rule orders the
     * values around its line, what a row is owed against it is the value beside the line: {@code 2 *
     * n <= 9} cuts between four and five and a row is written at four. Where a rule names a value,
     * the value is the line itself — and {@code 2 * n == 9} names no whole number at all, because
     * nine halved is not one.
     *
     * <p>Asked as "the value beside the line" for both, such a rule would single out four, and four
     * does not satisfy it. What keeps that from happening today is that a rule naming a value is
     * only ever read at a position it wrote the whole of, which is an invariant nothing states.
     */
    @Test
    void aRuleThatSinglesAValueOutSinglesOutAValueOrNoneAtAll() {
        Cutting names = new Cutting(
                new BorderQuantity.OverAForm("f", form("n", "2"), Map.of(term("n"), WHOLE)),
                new Level.ACount(new Count(new BigDecimal("9"))),
                new ComparisonClaim.Singled(true), null);

        assertEquals(term("n"), names.dividedPosition(),
                "twice a position is that position, whatever the rule says about it");
        assertEquals(null, names.singledValue(),
                "and no whole number is nine halved, so this names none of them");
    }

    /** And where the line is a value of the position, that value is the one it names. */
    @Test
    void andWhereTheLineIsAValueOfThePositionThatIsTheOneItNames() {
        Cutting names = new Cutting(
                new BorderQuantity.OverAForm("f", form("n", "2"), Map.of(term("n"), WHOLE)),
                new Level.ACount(new Count(new BigDecimal("8"))),
                new ComparisonClaim.Singled(true), null);

        assertEquals("4", names.singledValue().key(), "eight halved is four");
    }

    /**
     * A threshold the written form never reaches parts the values all the same.
     *
     * <p>{@code 2 * n <= 9} cuts a quantity whose values are the even numbers, and nine is not one
     * of them. The position's values part between four and five — which is where {@code n <= 4}
     * parts them, and is not a value the report can name by dividing nine by two.
     */
    @Test
    void aThresholdTheWrittenFormNeverReachesStillPartsTheValues() {
        Cutting closed = new Cutting(
                new BorderQuantity.OverAForm("f", form("n", "2"), Map.of(term("n"), WHOLE)),
                new Level.ACount(new Count(new BigDecimal("9"))),
                new ComparisonClaim.Cut(true, true), null);

        assertEquals("4|5", closed.seam().key());
    }
}
