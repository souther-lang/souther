package souther.compiler.inputs;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.values.TextExtents;

/**
 * The most a number can be because of what the language can hold, whatever any rule says.
 *
 * <p>A {@code String} holds no more than {@link TextExtents#LONGEST_STRING} code points, so no
 * length, class count or code point sum of one passes what that comes to. This is a limit on the
 * values a number takes, not a distinction a model draws: it narrows the run the number is read
 * over and states no line of its own.
 */
public final class RepresentationBounds {

    private static final String STRING = "String";

    private RepresentationBounds() {
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
            case NumericTerm.TakenOf taken when taken.operation().alias().equals(STRING) ->
                    TextExtents.LONGEST_STRING;
            case NumericTerm.TakenOf _, NumericTerm.ValueOf _, NumericTerm.CodePointAt _,
                 NumericTerm.TakenOver _, NumericTerm.OfAnElementsNeighbours _,
                 NumericTerm.OccurrencesOfItsValue _, NumericTerm.OccurrencesOfAKey _,
                 NumericTerm.GatheredUnderItsKey _, NumericTerm.GatheredUnderAKey _ -> null;
        };
    }

    /** The run {@link #mostOf} leaves {@code term}: open below, and ended above where it is. */
    public static NumericDomain.Bounds of(NumericTerm term) {
        Long most = mostOf(term);
        return most == null ? NumericDomain.Bounds.OPEN
                : new NumericDomain.Bounds(null, Endpoint.inclusive(Count.of(most)));
    }
}
