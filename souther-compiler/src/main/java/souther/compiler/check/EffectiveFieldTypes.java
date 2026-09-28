package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.Map;

/**
 * What each field a declaration reaches holds — the name of a field to the type it holds, over its
 * own fields and the ones its spreads bring in.
 *
 * <p>The closure and not one declaration's fields. A spread brings a field in with the type it was
 * written with, and a reader working that out for itself would be walking the spread declarations
 * again; so the walk is made once and what it came to is the answer.
 *
 * <p><b>A mapping and not a sequence.</b> The order this iterates in is the walk's and is no part
 * of what it answers, so nothing may take it as the order a value lays its fields out in or as the
 * order a declaration writes them. A reader that needs the order asks {@link FieldLayout}, which
 * answers it and is moved by an edit that only moves a field.
 *
 * <p><b>Types and nothing else.</b> Not where a field is written, not which declaration supplied
 * it, not whether two of them collided. Those are questions about the text of the declarations the
 * walk passed through, and a reader of this one is asking what a value of the type holds — an
 * answer that stays put when a declaration it reached moves.
 *
 * <p>Nothing here reports. A spread naming something that is not a product brings in no field and a
 * name declared twice keeps the one the walk reached last; both are refused where the declaration
 * is checked, against the text that wrote them, and a second refusal from out here would be about a
 * declaration the reader never read.
 *
 * <p>Beside {@link FieldBindings} rather than joined to it. Which binding a field is and what it
 * holds move at different times: a field's type changing leaves every binding where it was.
 */
@FunctionalInterface
public interface EffectiveFieldTypes {

    /**
     * What each field {@code declared} reaches holds, empty where it reaches none.
     *
     * <p>Asked of the declaration as the reader reached it, which is the name its own clauses were
     * written under.
     *
     * <p>Read by name. What comes back iterates, and in what order it does is not answered here.
     */
    Map<String, Type> of(TypeSymbol.AtModule declared);

    /** Nothing declared anywhere — for a reading over primitives, which asks of no declaration. */
    EffectiveFieldTypes NONE = _ -> Map.of();

    /**
     * The same walk over the declarations in {@code symbols}.
     *
     * <p>For a reading that has not been handed the compilation's answer. What a spread brings in
     * is decided by {@link FieldExpansion}, which both worlds read, so a reading made here and one
     * made from the store answer alike. What differs is what is said about a declaration that does
     * not hold together: {@link TypeOps#fieldTypes} refuses it, because it is the reading the
     * declaring module's own check is made of, and this is the one it is refused by.
     */
    static EffectiveFieldTypes asWritten(Symbols symbols) {
        return declared -> symbols.declaredNode(declared) instanceof Hir.Data data
                ? TypeOps.fieldTypes(data, symbols) : Map.of();
    }
}
