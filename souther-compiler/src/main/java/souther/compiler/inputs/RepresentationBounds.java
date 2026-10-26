package souther.compiler.inputs;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.types.ValueName;
import souther.compiler.values.TextExtents;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Map;

/**
 * The most a number can be because of what the language can hold, whatever any rule says.
 *
 * <p>A {@code String} holds no more than {@link TextExtents#LONGEST_STRING} code points, so no
 * length, class count or code point sum of one passes what that comes to. The numeric reading of a
 * term meets this into the term's own run ({@link NumericTerm#intrinsicBounds}), so a form over
 * several of them, a region and a line on any of these read one run; and the proof that a string
 * of a length can be written reads the same ceiling ({@link #mostOf}).
 */
public final class RepresentationBounds {

    private static final ValueName.Stdlib LENGTH = ValueName.Stdlib.operation("String", "length");

    /** Asked of every term of every form, so built once. */
    private static final NumericDomain.Bounds UP_TO_THE_LONGEST = atMost(TextExtents.LONGEST_STRING);

    private static final NumericDomain.Bounds UP_TO_THE_GREATEST_SUM =
            atMost(TextExtents.LONGEST_STRING * Character.MAX_CODE_POINT);

    private RepresentationBounds() {
    }

    /** Whether {@code taken} is how many code points a string holds. */
    public static boolean isALength(NumericTerm.TakenOf taken) {
        return taken.operation().equals(LENGTH);
    }

    /**
     * The most {@code term} can be, or null where nothing the language holds ends it. It is a
     * ceiling and not a claim that a string comes to it: a sum of code points reaches the product
     * of the longest string and the last code point only if one string is all of the last one.
     */
    public static Long mostOf(NumericTerm term) {
        return switch (term) {
            case NumericTerm.CodePointValueSum _ ->
                    TextExtents.LONGEST_STRING * Character.MAX_CODE_POINT;
            case NumericTerm.CodePointClassCount _ -> TextExtents.LONGEST_STRING;
            case NumericTerm.TakenOf taken when isALength(taken) -> TextExtents.LONGEST_STRING;
            case NumericTerm.TakenOf _, NumericTerm.ValueOf _, NumericTerm.CodePointAt _,
                 NumericTerm.TakenOver _, NumericTerm.OfAnElementsNeighbours _,
                 NumericTerm.OccurrencesOfItsValue _, NumericTerm.OccurrencesOfAKey _,
                 NumericTerm.GatheredUnderItsKey _, NumericTerm.GatheredUnderAKey _ -> null;
        };
    }

    /** The run {@link #mostOf} leaves {@code term}: open below, and ended above where it is. */
    public static NumericDomain.Bounds of(NumericTerm term) {
        Long most = mostOf(term);
        if (most == null) {
            return NumericDomain.Bounds.OPEN;
        }
        return most == TextExtents.LONGEST_STRING ? UP_TO_THE_LONGEST : UP_TO_THE_GREATEST_SUM;
    }

    /**
     * Where a form over terms can lie because of what the language holds of each of them: each term
     * within the run {@link NumericTerm#reachBounds} gives it, weighed and added.
     *
     * <p>Open where no term of the form is ended by the language, so a form of numbers nothing ends
     * says nothing here; and open on a side where some term that decides that side has no end
     * there. A weight that is not whole leaves the form open, which holds every value it could.
     */
    public static NumericDomain.Bounds ofAForm(LinearForm<NumericTerm> form) {
        boolean ended = false;
        BigInteger low = BigInteger.ZERO;
        BigInteger high = BigInteger.ZERO;
        boolean lowHeld = true;
        boolean highHeld = true;
        for (Map.Entry<NumericTerm, ExactRatio> each : form.coefs().entrySet()) {
            if (!each.getValue().isWhole()) {
                return NumericDomain.Bounds.OPEN;
            }
            BigInteger weight = each.getValue().floor().orNull();
            ended |= mostOf(each.getKey()) != null;
            NumericDomain.Bounds reach = each.getKey().reachBounds();
            BigInteger least = wholeAt(reach.min());
            BigInteger most = wholeAt(reach.max());
            BigInteger lowest = weight.signum() >= 0 ? least : most;
            BigInteger highest = weight.signum() >= 0 ? most : least;
            lowHeld &= lowest != null;
            highHeld &= highest != null;
            low = lowest == null ? low : low.add(weight.multiply(lowest));
            high = highest == null ? high : high.add(weight.multiply(highest));
        }
        if (!ended || !(lowHeld || highHeld)) {
            return NumericDomain.Bounds.OPEN;
        }
        return new NumericDomain.Bounds(
                lowHeld ? Endpoint.inclusive(Count.of(new BigDecimal(low))) : null,
                highHeld ? Endpoint.inclusive(Count.of(new BigDecimal(high))) : null);
    }

    /** The whole number {@code end} stands at, or null where there is no end or it is no whole
     *  count. */
    private static BigInteger wholeAt(Endpoint end) {
        return end != null && end.at() instanceof Count count && count.whole()
                ? count.exactly().floor().orNull() : null;
    }

    private static NumericDomain.Bounds atMost(long most) {
        return new NumericDomain.Bounds(null, Endpoint.inclusive(Count.of(most)));
    }
}
