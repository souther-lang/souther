package souther.compiler.observe;

import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.Map;

/**
 * What a declared data's fields hold.
 *
 * <p>One declaration's own layout, and nothing about a type. What is asked here is what a value of
 * <em>this declaration</em> is laid out as, so a caller has already settled which declaration it is
 * walking — the case a value turned out to be, the newtype a name was taken off. A whole declaration
 * and not one field of it, because the fields of one are an order as much as a set: a value is laid
 * out in it, and a reader writing a value's parts out follows it.
 *
 * <p><b>Not what a {@code .} may name.</b> {@code souther.compiler.check.FieldRead} answers that,
 * and it is the only thing that crosses a {@code .} on a type. The two are the same map at a record
 * and are not the same question: a sum lays out no field of its own, and a name every one of its
 * cases spreads is readable on every value of it. Asked here, that name comes back as a field
 * nothing declares — which is a true answer to this question and the wrong answer to that one.
 *
 * <p><b>What keeps that apart is the census over the callers of {@link #of}, and not this type.</b>
 * A reader holding a position can still spell {@code of(ref.name())} and get the layout, and one
 * did — the snapshot an editor asks what may follow a {@code .} was written that way and offered an
 * author nothing where the language reads a shared name. Both worlds are keyed by the declaration's
 * name, which is what a {@code Type.Ref} carries, so a key this could take that a position could not
 * be turned into does not exist. {@code NoQuestionAboutAShapeIsAnsweredOutOfAnothersAnswerTest}
 * holds the callers of this method as an exact set instead, and a reader that arrives is a finding
 * there rather than a silence here.
 *
 * <p>Whoever holds the declarations answers it, and a reader may not work one out beside them. A
 * checked program's fields are what its check settled ({@code core.ValueShape}); an editor reading
 * a text that has not checked answers from what its declarations resolve to so far. Those are two
 * worlds and not two accounts of one: what a reader is handed says which world it is reading in,
 * and no reader in the accepted one may fall back to reading declarations itself when the checked
 * answer is missing.
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
}
