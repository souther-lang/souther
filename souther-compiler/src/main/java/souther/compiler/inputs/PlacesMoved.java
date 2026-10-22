package souther.compiler.inputs;

import java.util.function.UnaryOperator;

/**
 * Where a move puts each place a number is read off.
 *
 * <p>Every place is put somewhere: a number of one place moved is a number of one place, and a
 * number that is no such number where its places are put says so itself, by answering null from
 * {@link NumericTerm#movedTo}. So the move answers no null, and a function that does is stopped
 * where it answers, before any number is built of what it put nowhere.
 */
public final class PlacesMoved {

    private static final PlacesMoved NOWHERE = new PlacesMoved(UnaryOperator.identity());

    private final UnaryOperator<TermPath> where;

    private PlacesMoved(UnaryOperator<TermPath> where) {
        this.where = where;
    }

    /** The move putting each place where {@code where} answers. */
    public static PlacesMoved by(UnaryOperator<TermPath> where) {
        if (where == null) {
            throw new IllegalArgumentException("a move puts each place somewhere");
        }
        return new PlacesMoved(where);
    }

    /** The move leaving every place where it is. */
    public static PlacesMoved nowhere() {
        return NOWHERE;
    }

    /** Where this puts {@code place}. */
    public TermPath put(TermPath place) {
        TermPath at = where.apply(place);
        if (at == null) {
            throw new IllegalStateException("a move put " + place + " nowhere; every place is put"
                    + " somewhere, and a number with no such number there answers null itself");
        }
        return at;
    }

    /** Whether this leaves {@code place} where it is. */
    public boolean leaves(TermPath place) {
        return put(place).equals(place);
    }
}
