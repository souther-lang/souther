package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Towards;

import java.util.Objects;

/**
 * A value a behavior compares an input against, and which side of it the value itself falls on.
 *
 * <p>This is what actually divides the values a row can write. A type's invariant does not — everything
 * outside it is refused at construction — but {@code cost <= 100000} leaves two ranges a row can reach,
 * and which one it lands in is what the behavior does differently.
 *
 * @param term    the number compared, which is a location's content or something taken of it —
 *                {@code String.length(t.name)} draws a line as {@code t.size} does
 * @param parts   where the values part: the last value on one side, the first on the other, and the
 *                place the line falls at. Held as the division rather than as the number the rule
 *                carried, because two rules can part a position's values in one place and because
 *                a rule that wrote a multiple of the position may part them where the position
 *                holds no value at all — {@code 3 * d <= 1} cuts at a third, and the behavior tells
 *                the values either side of it apart whether or not this language can write one
 * @param origin  the rule that drew it, which is a {@code guard} of a body or a comparison written
 *                in an {@code ensures}. Both leave values a row can write either side; what differs
 *                is what meeting the line takes, and that is the origin's to answer
 */
public record Threshold(NumericTerm.FromOnePosition term, Seam parts, Towards valueBelongs,
                        OriginRef origin) {

    /** A side and not the absence of one, for the reason a cut's own is
     *  ({@link souther.compiler.check.ComparisonClaim.Cut}): a line with no side reads as one
     *  whose value falls above it, and asks for a row against the wrong neighbour. */
    public Threshold {
        Objects.requireNonNull(valueBelongs, "which side of the line its own value falls on");
    }

    /**
     * Where a row is owed against this line, as a value of the position, or null where the position
     * has none either side of it.
     *
     * <p>The value the classes meet at and not the place the line falls: {@code 2 * n <= 9} parts
     * the whole numbers at four and a half, and what a row is written at is four. Which of the two
     * values beside the line it is turns on the side the rule put its own value on, which is the
     * rule's to say and not the seam's — two rules that part the values in one place can put it on
     * opposite sides and are still one division.
     *
     * <p>Null is not "no line". It is a line the position has no value beside, which divides it all
     * the same and has no row to be owed at: {@code 3 * d <= 1} cuts at a third, and no decimal is
     * a third or the decimal next to one.
     */
    public Place value() {
        Level beside = valueBelongs == Towards.BELOW ? parts.below() : parts.above();
        return beside instanceof Level.OnACarrier on ? on.at() : null;
    }

    /** Where the value this line is drawn on sits. Not what the line is drawn on: that is
     * {@link #term()}, and two terms can be taken of one location. */
    public TermPath path() {
        return term.position();
    }
}
