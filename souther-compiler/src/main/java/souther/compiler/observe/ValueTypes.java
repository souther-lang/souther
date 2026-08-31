package souther.compiler.observe;

import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

/**
 * What a declaration says stands at one place inside a value.
 *
 * <p>The whole of what comparing two values needs of the declarations. A comparison reads a value
 * against another and descends where both have parts, and the one thing it cannot read off either
 * of them is what the enclosing type declares a field to be — which is what says whether a sequence
 * there is ordered, and what a value at that place is a value of.
 *
 * <p>One reading and not one per reader. What a field holds is {@link FieldTypes}' answer, and this
 * is that answer as a place: whoever holds the declarations answers the question once, and this
 * compile and a snapshot of it read the same answer through the same step. Written the other way —
 * each side turning its own declarations into places — the two would agree only for as long as
 * neither walk forgot a rule, and the day one did, a row would hold where it was compiled and fail
 * where it was published.
 */
public final class ValueTypes {

    private final FieldTypes fields;

    private ValueTypes(FieldTypes fields) {
        if (fields == null) {
            throw new IllegalArgumentException(
                    "a place inside a value is read from what a declaration says its fields hold");
        }
        this.fields = fields;
    }

    /** The places {@code fields} describes. */
    public static ValueTypes over(FieldTypes fields) {
        return new ValueTypes(fields);
    }

    /**
     * Where {@code owner} declares {@code field} to be read, or {@link Position#UNREAD} where it
     * declares no such field.
     *
     * <p>A newtype's single {@code value} is answered the same way, since that is the field it is
     * written with.
     */
    public Position field(TypeSymbol owner, String field) {
        Type declared = fields.field(owner, field);
        return declared == null ? Position.UNREAD : Position.at(declared);
    }
}
