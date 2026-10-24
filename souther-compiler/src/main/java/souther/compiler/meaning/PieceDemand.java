package souther.compiler.meaning;

import souther.compiler.inputs.TermPath;
import souther.compiler.types.Type;

import java.util.Objects;

/**
 * A piece of the string at {@code position}, parted at {@code separator}, that a body hands to the
 * attempted construction of {@code attempted}.
 *
 * <p>One flow and not three facts: it is this string that is parted here and this type that its
 * pieces are then built as. A body that parts one string and builds one type out of another's
 * pieces states two of these, and neither is the other's.
 *
 * @param position  where the string stands, as the input reading names the place
 * @param separator the code point the string is parted at
 * @param attempted the newtype whose construction is attempted of a piece
 */
public record PieceDemand(TermPath position, int separator, Type attempted) {

    public PieceDemand {
        Objects.requireNonNull(position, "a string that is parted stands somewhere");
        Objects.requireNonNull(attempted, "a piece is built as some type");
    }
}
