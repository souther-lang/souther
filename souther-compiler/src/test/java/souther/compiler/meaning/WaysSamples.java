package souther.compiler.meaning;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * Statements over the ways the elements of a container are kept, small enough to say what their
 * cases are: one element, kept by one truth.
 */
public final class WaysSamples {

    private WaysSamples() {
    }

    /**
     * The ways of keeping one element by one truth that states {@code condition}, the comparison
     * over its total being that the total is at least one: it holds in the way that keeps the
     * element and fails in the other, so the cases come to {@code condition}.
     */
    public static Proposition.WaysToWrite ofOneTruth(Proposition condition) {
        Quantity.TheKeptTotal sum = new Quantity.TheKeptTotal(0, false);
        LinearForm<Quantity> form = LinearForm.<Quantity>atom(sum)
                .plus(LinearForm.<Quantity>constant(ExactRatio.of(-1))).orNull();
        Relation.OneWay<Quantity> oneWay = Relation.OneWay.of(form, Rel.GE);
        Proposition atLeastOne = Proposition.compared(
                new Relation.Affine(oneWay.form(), oneWay.proposition()), oneWay.holds());
        return new Proposition.WaysToWrite(
                new KeptWays(List.of(List.of(new KeptWays.Keep(0, true))), 1),
                Map.of(0, condition), atLeastOne,
                List.of(LinearForm.constant(ExactRatio.ONE)), sum,
                Optional.empty(), 0, false, Optional.empty(), 0, 3);
    }

    /** The statement over the ways {@link #ofOneTruth} holds. */
    public static Proposition.OfTheWays over(Proposition condition) {
        return new Proposition.OfTheWays(ofOneTruth(condition), true);
    }
}
