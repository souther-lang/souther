package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.core.ValueShape;
import souther.compiler.observe.FieldTypes;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * What the check settled a declared data's fields hold.
 *
 * <p>The accepted program's reading, and the only one anything running its rows may have. What a
 * value of a declaration is made of is decided once, where the declaration is checked
 * ({@link ExecutableInvariants}); every reader here projects that decision and none re-reads the
 * declaration it came from. So a row compared against a field and a text typed by the same field
 * are held to one answer, and the JVM refusing a construction is refusing it by that answer too.
 *
 * <p>Which declaration a shape is asked for is the declaration's own identity: a data a module
 * wrote names the module that wrote it, and that is the compile's answer to ask. Nothing is
 * searched for — there is no order in which this module's declarations are tried before the ones it
 * imports — so two data of one name declared in two modules cannot be confused for one another.
 *
 * <p>A missing shape is not an absent field. Where a declaration is a product and the check has no
 * answer about it, this refuses to answer rather than saying the product has no such field: read as
 * an absence, a value of it would be compared as whatever its parts happen to look like, and a row
 * about it would mean one thing here and another wherever the shape was in hand. Nothing falls back
 * to reading the declaration.
 */
public final class CheckedFieldTypes implements FieldTypes {

    /** What each declaration was checked to be, asked for by the declaration's own identity. */
    public interface Shapes {

        /** What a value of {@code declared} is made of, or null where this compile settled nothing
         *  about it. */
        ValueShape of(TypeSymbol.AtModule declared);
    }

    private final Symbols symbols;
    private final Shapes shapes;

    public CheckedFieldTypes(Symbols symbols, Shapes shapes) {
        if (symbols == null || shapes == null) {
            throw new IllegalArgumentException("a checked field is a declaration and what the check"
                    + " said about it: " + symbols + " " + shapes);
        }
        this.symbols = symbols;
        this.shapes = shapes;
    }

    @Override
    public Map<String, Type> of(TypeSymbol owner) {
        // A declaration the language gives is a primitive or a case of a sum, and neither is a data
        // a value is built out of field by field.
        if (!(owner instanceof TypeSymbol.AtModule declared)
                || !(symbols.declarations().declaration(declared) instanceof Hir.Data)) {
            return Map.of();
        }
        ValueShape shape = shapes.of(declared);
        if (shape == null) {
            throw new IllegalStateException("`" + declared + "` is a data this compile resolved and"
                    + " the check said nothing about what a value of it is made of");
        }
        Map<String, Type> out = new LinkedHashMap<>();
        for (ValueShape.Field field : shape.fields()) {
            out.put(field.name(), field.type());
        }
        return out;
    }
}
