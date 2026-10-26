package souther.compiler.inputs;

import souther.compiler.check.DeclaredArgument;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.ResultBound;
import souther.compiler.types.ValueName;
import souther.compiler.values.TextExtents;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Map;
import java.util.Optional;
import java.util.concurrent.ConcurrentHashMap;

/**
 * The most a number can be because of what the language can hold, whatever any rule says.
 *
 * <p>A {@code String} holds no more than {@link TextExtents#LONGEST_STRING} code points, so no
 * length, class count or code point sum of one passes what that comes to. The number is not kept
 * here: {@code String.length} declares where it stops ({@code OperationFacts}), and this reads that
 * declaration, as it does for any operation that declares an end of the representation.
 *
 * <p>Two readers ask it, and neither is the run the rules leave a term. Whether a value can stand
 * at a level or on a side of it, and which points of a line can be written, ask the quantity a
 * line is on ({@code BorderQuantity#heldByTheLanguage}, which weighs {@link #ofAForm} of its
 * terms). The proof that a string of a length can be written reads the same ceiling
 * ({@link #mostOf}).
 *
 * <p>It is not met into {@link NumericTerm#intrinsicBounds}, which is where the classes of a
 * position and the ends of its runs are drawn from. The longest string is where strings stop and
 * no distinction a model made: met in there, a relation between two lengths holds it as a class of
 * its own, which only a string of that length can fill. A new reader of a term's values chooses
 * between the two by what it answers, whether a value can stand or what a position is divided
 * into.
 */
public final class RepresentationBounds {

    private static final ValueName.Stdlib LENGTH = ValueName.Stdlib.operation("String", "length");

    /** The run up to each end declared. Asked of every term of every form, and there are only as
     *  many as there are ends declared, so each is built once. */
    private static final Map<Long, NumericDomain.Bounds> UP_TO = new ConcurrentHashMap<>();

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
            case NumericTerm.CodePointValueSum _ -> times(longestString(), Character.MAX_CODE_POINT);
            case NumericTerm.CodePointClassCount _ -> longestString();
            case NumericTerm.TakenOf taken -> whereItsOperationStops(taken.operation());
            case NumericTerm.ValueOf _, NumericTerm.CodePointAt _,
                 NumericTerm.TakenOver _, NumericTerm.OfAnElementsNeighbours _,
                 NumericTerm.OccurrencesOfItsValue _, NumericTerm.OccurrencesOfAKey _,
                 NumericTerm.GatheredUnderItsKey _, NumericTerm.GatheredUnderAKey _ -> null;
        };
    }

    /** The most code points a string holds, as {@code String.length} declares where it stops, or
     *  null where it declares none. The code points and the classes of a string are counted from
     *  the same string, so they stop where its length does. */
    private static Long longestString() {
        return whereItsOperationStops(LENGTH);
    }

    /** {@code number} times {@code by}, or null where {@code number} is. */
    private static Long times(Long number, long by) {
        return number == null ? null : number * by;
    }

    /** Where {@code operation} says its answers stop, as it declares it, or null where it declares
     *  no such end. An end the classes of a position are drawn to is not one: that is already in
     *  {@link NumericTerm#intrinsicBounds}, and this is what the language holds beyond it. */
    private static Long whereItsOperationStops(ValueName operation) {
        Long stops = null;
        for (ResultBound<DeclaredArgument> row
                : DefaultBoundOperationFacts.get().everyBoundOnTheResult(operation)) {
            if (row.isWhereTheRepresentationStops() && !row.isDrawnTo() && row.against() == null
                    && row.rel() == Rel.LE && row.offset().scale() == 0
                    && row.offset().unscaledValue().bitLength() < Long.SIZE) {
                long at = row.offset().longValue();
                stops = stops == null ? at : Math.min(stops, at);
            }
        }
        return stops;
    }

    /** The run {@link #mostOf} leaves {@code term}: open below, and ended above where it is. */
    public static NumericDomain.Bounds of(NumericTerm term) {
        Long most = mostOf(term);
        return most == null ? NumericDomain.Bounds.OPEN : UP_TO.computeIfAbsent(most,
                RepresentationBounds::atMost);
    }

    /**
     * Where a form over terms can lie because of what the language holds of each of them: each term
     * within the run {@link NumericTerm#reachBounds} gives it, weighed and added.
     *
     * <p>Open where no term of the form is ended by the language, so a form of numbers nothing ends
     * says nothing here; and open on a side where some term that decides that side has no end
     * there. A weight may be any ratio: the ends are worked out exactly and kept as they are where
     * a count writes them, and otherwise written as the whole numbers they lie within, the lower
     * one rounded down and the upper one up, so the run holds every value the form could and
     * never fewer.
     *
     * <p>This is what the language holds, to be asked whether a value can stand and never what a
     * position is divided into. The run the rules leave a term, with the language's ends met in, is
     * {@link NumericTerm#reachBounds}; it is not the term's {@link NumericTerm#intrinsicBounds},
     * and a reader that wants where the classes of a position run to wants the second.
     */
    public static NumericDomain.Bounds ofAForm(LinearForm<NumericTerm> form) {
        boolean ended = false;
        ExactRatio low = ExactRatio.ZERO;
        ExactRatio high = ExactRatio.ZERO;
        boolean lowHeld = true;
        boolean highHeld = true;
        for (Map.Entry<NumericTerm, ExactRatio> each : form.coefs().entrySet()) {
            ExactRatio weight = each.getValue();
            ended |= mostOf(each.getKey()) != null;
            NumericDomain.Bounds reach = each.getKey().reachBounds();
            ExactRatio least = numberAt(reach.min());
            ExactRatio most = numberAt(reach.max());
            ExactRatio lowest = weight.signum() >= 0 ? least : most;
            ExactRatio highest = weight.signum() >= 0 ? most : least;
            lowHeld &= lowest != null;
            highHeld &= highest != null;
            low = lowest == null ? low : sum(low, weight, lowest);
            high = highest == null ? high : sum(high, weight, highest);
            if (low == null || high == null) {
                return NumericDomain.Bounds.OPEN;
            }
        }
        if (!ended || !(lowHeld || highHeld)) {
            return NumericDomain.Bounds.OPEN;
        }
        return new NumericDomain.Bounds(lowHeld ? endpoint(low, false) : null,
                highHeld ? endpoint(high, true) : null);
    }

    /**
     * {@code at} as an end: the count that writes it exactly where there is one, and otherwise the
     * whole number just outside it, so the run never holds fewer values than the form could.
     * Null where neither can be written, which leaves that side open.
     */
    private static Endpoint endpoint(ExactRatio at, boolean upper) {
        Optional<Count> exact = Count.written(at).orNull();
        if (exact != null && exact.isPresent()) {
            return Endpoint.inclusive(exact.get());
        }
        BigInteger outside = (upper ? at.ceiling() : at.floor()).orNull();
        return outside == null ? null : Endpoint.inclusive(Count.of(new BigDecimal(outside)));
    }

    /** {@code so far} and {@code weight} times {@code by}, or null where the exact arithmetic
     *  holds no such number. */
    private static ExactRatio sum(ExactRatio soFar, ExactRatio weight, ExactRatio by) {
        ExactRatio product = weight.times(by).orNull();
        return product == null ? null : soFar.plus(product).orNull();
    }

    /** The number {@code end} stands at, or null where there is no end or it is at no count. */
    private static ExactRatio numberAt(Endpoint end) {
        return end != null && end.at() instanceof Count count ? count.exactly() : null;
    }

    private static NumericDomain.Bounds atMost(long most) {
        return new NumericDomain.Bounds(null, Endpoint.inclusive(Count.of(most)));
    }
}
