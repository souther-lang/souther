package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A rule whose positions have all cancelled is arithmetic, and arithmetic is already answered.
 *
 * <p>{@code 0 >= 1} restricts nothing because nothing is left for it to restrict: it is the
 * assertion that the number the sum came to stands the stated way to nought, and that is settled
 * the moment it is read. So the constraint algebra hands back neither a rule nor a refusal to read
 * one, but which of the two extremes the assertion is.
 *
 * <p><b>Which way the constant stands is which way the sum stands to nought.</b> The assertion is
 * {@code Σ coefs·atom + constant rel 0}, so with no atoms left the constant is what the left side
 * of the comparison came to and nought is the right. A reading that took it the other way round
 * would answer every one of these backwards, and every arm of the table below is what tells the two
 * apart.
 *
 * <p>Written out rather than worked out, so that a reading which comes to these answers by another
 * route is held to the same table rather than to its own rule.
 */
class AComparisonNamingNoPositionIsSettledByItsConstantTest {

    /** What the constant came to, what the rule states of it, and which extreme that is. */
    private record Row(long constant, NumericDomain.Rel rel, boolean holds) {

        String asked() {
            return constant + " " + rel + " 0";
        }
    }

    private static Row row(long constant, NumericDomain.Rel rel, boolean holds) {
        return new Row(constant, rel, holds);
    }

    private static final List<Row> ROWS = List.of(
            row(-1, NumericDomain.Rel.LE, true),
            row(0, NumericDomain.Rel.LE, true),
            row(1, NumericDomain.Rel.LE, false),
            row(-1, NumericDomain.Rel.LT, true),
            row(0, NumericDomain.Rel.LT, false),
            row(1, NumericDomain.Rel.LT, false),
            row(-1, NumericDomain.Rel.GE, false),
            row(0, NumericDomain.Rel.GE, true),
            row(1, NumericDomain.Rel.GE, true),
            row(-1, NumericDomain.Rel.GT, false),
            row(0, NumericDomain.Rel.GT, false),
            row(1, NumericDomain.Rel.GT, true),
            row(-1, NumericDomain.Rel.EQ, false),
            row(0, NumericDomain.Rel.EQ, true),
            row(1, NumericDomain.Rel.EQ, false),
            row(-1, NumericDomain.Rel.NE, true),
            row(0, NumericDomain.Rel.NE, false),
            row(1, NumericDomain.Rel.NE, true));

    /** Every relation at each of the three ways its constant can stand. The table is what both
     *  halves of the test below are read out of, so a row taken out of it goes from the answers as
     *  well and nothing else would say so. */
    @Test
    void everyRelationIsAskedAboutAtEachSign() {
        assertEquals(NumericDomain.Rel.values().length * 3, ROWS.size());
    }

    @Test
    void whichExtremeAnAssertionWithoutPositionsIsReadAsIsWhichWayItsConstantStands() {
        List<String> expected = new ArrayList<>();
        ROWS.forEach(each -> expected.add(each.asked() + ": " + said(each.holds())));

        List<String> answered = new ArrayList<>();
        for (Row each : ROWS) {
            AffineConstraint.Read<String> read = AffineConstraint.of(Map.of(),
                    Rational.of(each.constant()), each.rel(), atom -> Granularity.DISCRETE);
            answered.add(each.asked() + ": " + read.getClass().getSimpleName());
        }

        assertEquals(expected, answered);
    }

    private static String said(boolean holds) {
        return holds ? "HoldsAlways" : "HoldsNever";
    }
}
