package souther.compiler.meaning;

import souther.compiler.inputs.TermPath;
import souther.compiler.semantics.CaseMapping;
import souther.compiler.types.Type;

import java.util.Objects;

/**
 * A piece of the string at {@code position}, made into {@code through} and parted at
 * {@code separator}, that a body hands to the attempted construction of {@code attempted}.
 *
 * <p>One flow and not three facts: it is this string that is parted here and this type that its
 * pieces are then built as. A body that parts one string and builds one type out of another's
 * pieces states two of these, and neither is the other's.
 *
 * <p>What the string was made into before it was parted is part of the flow. The pieces the type is
 * built of are the pieces of the converted string, so a reader asking which strings of the position
 * the flow is about asks it of the conversion as well as of the type.
 *
 * @param position  where the string stands, as the input reading names the place
 * @param through   the case conversions the string goes through before it is parted
 * @param separator the code point the string is parted at
 * @param attempted the newtype whose construction is attempted of a piece
 */
public record PieceDemand(TermPath position, CaseMapping through, int separator, Type attempted) {

    public PieceDemand {
        Objects.requireNonNull(position, "a string that is parted stands somewhere");
        Objects.requireNonNull(through, "a string is made into itself, or into what is said");
        Objects.requireNonNull(attempted, "a piece is built as some type");
    }
}
