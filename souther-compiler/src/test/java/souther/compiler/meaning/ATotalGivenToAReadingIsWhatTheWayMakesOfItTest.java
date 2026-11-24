package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison read once over the total of the elements a way keeps and how many it keeps states,
 * in each way, the comparison of what that way makes of them: a way that makes both numbers
 * decides it, and a way that leaves the total to the input states a line on it.
 */
class ATotalGivenToAReadingIsWhatTheWayMakesOfItTest {

    private static final Quantity SUM = new Quantity.TheKeptTotal(1, false);
    private static final Quantity COUNT = new Quantity.TheKeptTotal(1, true);
    private static final Quantity INPUT = new Quantity.TheKeptTotal(2, false);

    /** {@code total - 100 * count >= 0}: the mean of the kept elements is at least a hundred. */
    private static Proposition meanAtLeastAHundred() {
        LinearForm<Quantity> form = LinearForm.<Quantity>atom(SUM)
                .plus(LinearForm.<Quantity>weighing(COUNT, ExactRatio.of(-100))).orNull();
        Relation.OneWay<Quantity> oneWay = Relation.OneWay.of(form, Rel.GE);
        return Proposition.compared(
                new Relation.Affine(oneWay.form(), oneWay.proposition()), oneWay.holds());
    }

    private static Proposition given(Proposition stated,
                                     Map<Quantity, LinearForm<Quantity>> totals) {
        return switch (GivenTotals.in(stated, totals)) {
            case ExactAnswer.Held<Proposition>(var held) -> held;
            case ExactAnswer.Unheld<Proposition>(var why) ->
                    throw new AssertionError("a number is held: " + why);
        };
    }

    @Test
    void aWayThatMakesBothNumbersDecidesTheComparison() {
        Proposition held = given(meanAtLeastAHundred(), Map.of(
                SUM, LinearForm.constant(ExactRatio.of(250)),
                COUNT, LinearForm.constant(ExactRatio.of(2))));
        assertEquals(new Proposition.Always(true), held);
        Proposition failed = given(meanAtLeastAHundred(), Map.of(
                SUM, LinearForm.constant(ExactRatio.of(150)),
                COUNT, LinearForm.constant(ExactRatio.of(2))));
        assertEquals(new Proposition.Always(false), failed);
    }

    @Test
    void aWayThatLeavesTheTotalToTheInputStatesALineOnIt() {
        Proposition line = given(meanAtLeastAHundred(), Map.of(
                SUM, LinearForm.atom(INPUT),
                COUNT, LinearForm.constant(ExactRatio.of(2))));
        Proposition.Compared compared = assertInstanceOf(Proposition.Compared.class, line);
        Relation.Affine affine = assertInstanceOf(Relation.Affine.class, compared.relation());
        assertEquals(Map.of(INPUT, ExactRatio.ONE), affine.form().coefs());
        assertEquals(ExactRatio.of(-200), affine.form().constant());
    }

    @Test
    void aStatementWithNoTotalInItIsTheSameStatement() {
        Proposition alone = new Proposition.Always(true);
        assertEquals(alone, given(alone, Map.of(SUM, LinearForm.constant(ExactRatio.ONE))));
    }

    @Test
    void onlyAStatementOfRelationsAndTheirJoinsCanBeGivenATotal() {
        assertTrue(GivenTotals.canBeGiven(Proposition.all(List.of(meanAtLeastAHundred(),
                meanAtLeastAHundred().denied()))));
        assertFalse(GivenTotals.canBeGiven(new Proposition.Unread(Optional.empty(), 0,
                new WhyUnread.NotArithmetic(), false, true)));
    }
}
