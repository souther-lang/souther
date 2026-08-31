package souther.compiler.observe;

import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.Map;

/**
 * What a declared data's fields hold.
 *
 * <p>The one question anything reading a value's parts asks of the declarations, and the only one:
 * given the declaration a value is of, what each field of it contains. Where a reader takes a field
 * of a value, decides what order a sequence there is compared on, or types the {@code x.field} a
 * text wrote, this is what it asks — so the answer a comparison is made against and the answer a
 * projection is typed by are the same answer.
 *
 * <p>Whoever holds the declarations answers it, and a reader may not work one out beside them. A
 * checked program's fields are what its check settled ({@code core.ValueShape}); an editor reading
 * a text that has not checked answers from what its declarations resolve to so far. Those are two
 * worlds and not two accounts of one: what a reader is handed says which world it is reading in,
 * and no reader in the accepted one may fall back to reading declarations itself when the checked
 * answer is missing.
 *
 * <p>{@link #of} answers for a whole declaration because the fields of one are an order as much as
 * a set: a value is laid out in it, and a reader writing a value's parts out follows it. A reader
 * after one field asks for one ({@link #field}), and the two cannot disagree because the second is
 * the first.
 */
public interface FieldTypes {

    /**
     * The fields the declarations of an accepted program are made of.
     *
     * <p>The one step from a declaration to the fields under it, written here and not in either
     * world. What a reader has in hand is a type, and only a module writes a declaration a value is
     * built field by field out of — so what the language gives has no fields, which is an answer,
     * and everything else is what the world says it is made of. Written in each world instead, the
     * step would be two readings of one thing, and the one that read an absence as a declaration
     * with no fields would be the one nobody noticed.
     */
    static FieldTypes over(Declarations declarations) {
        return owner -> owner instanceof TypeSymbol.AtModule declared
                && declarations.of(declared) instanceof Composed.OfFields(Map<String, Type> fields)
                ? fields : Map.of();
    }

    /**
     * Every field a value of {@code owner} holds, in the order a value of it is laid out.
     *
     * <p>Empty for anything that is not a declared product — a sum, a unit, a type the language
     * gives — which is an answer and not a failure: none of them is a place a field stands under.
     * A newtype is a product of the one field it is written with, and is answered like any other.
     */
    Map<String, Type> of(TypeSymbol owner);

    /** What {@code owner} declares its {@code field} to hold, or null where it declares no such
     *  field. */
    default Type field(TypeSymbol owner, String field) {
        return of(owner).get(field);
    }
}
