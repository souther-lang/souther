package souther.compiler.partition;

import souther.compiler.check.OriginRef;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Place;

/**
 * A value a behavior compares an input against, and which side of it the value itself falls on.
 *
 * <p>This is what actually divides the values a row can write. A type's invariant does not — everything
 * outside it is refused at construction — but {@code cost <= 100000} leaves two ranges a row can reach,
 * and which one it lands in is what the behavior does differently.
 *
 * @param term             the number compared, which is a location's content or something taken of
 *                         it — {@code String.length(t.name)} draws a line as {@code t.size} does
 * @param value            where the behavior changes
 * @param valueBelongsBelow whether {@code value} itself is on the low side. {@code x <= c} puts it
 *                          there; {@code x < c} puts it on the high side. Getting this wrong moves
 *                          the boundary by one and asks for a row that proves nothing.
 * @param origin           the rule that drew it, which is a {@code guard} of a body or a comparison
 *                         written in an {@code ensures}. Both leave values a row can write either
 *                         side; what differs is what meeting the line takes, and that is the
 *                         origin's to answer
 */
public record Threshold(NumericTerm term, Place value, boolean valueBelongsBelow,
                        OriginRef origin) {

    /** Where the value this line is drawn on sits. Not what the line is drawn on: that is
     * {@link #term()}, and two terms can be taken of one location. */
    public TermPath path() {
        return term.path();
    }
}
