package souther.compiler.observe;

import souther.compiler.types.TypeSymbol;

/**
 * What a declaration says stands at one place inside a value.
 *
 * <p>The whole of what comparing two values needs of the declarations. A comparison reads a value
 * against another and descends where both have parts, and the one thing it cannot read off either
 * of them is what the enclosing type declares a field to be — which is what says whether a sequence
 * there is ordered, and what a value at that place is a value of.
 *
 * <p>One question and not a set of declarations. Handed the declarations themselves, a comparison
 * would be free to read them for anything, and what it read would be whatever the compiler that
 * answered happened to hold. Asked as one question, whoever answers it is whoever holds the
 * declarations — this compile's own reading of what it parsed, or a snapshot's reading of what it
 * carries — and neither can make the comparison answer differently about the same value.
 */
public interface ValueTypes {

    /**
     * Where {@code owner} declares {@code field} to be read, or {@link Position#UNREAD} where it
     * declares no such field.
     *
     * <p>A newtype's single {@code value} is answered the same way, since that is the field it is
     * written with.
     */
    Position field(TypeSymbol owner, String field);
}
