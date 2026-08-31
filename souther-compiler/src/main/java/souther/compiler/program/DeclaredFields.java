package souther.compiler.program;

import souther.compiler.core.ValueShape;
import souther.compiler.observe.Composed;
import souther.compiler.observe.Declarations;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * What this program says each of its declarations is made of.
 *
 * <p>Answered from the declarations this program publishes and from nothing else. So a row read
 * against an answer here is read against exactly what a reader of {@link CheckedProgram#declaration}
 * would lay a value out by, and the two cannot come apart.
 *
 * <p>Over every declaration this compile resolved, its own modules' and the language's and a
 * dependency's alike: a value stated for one module's behavior may hold a value of another's, and a
 * reader that could not read the second would read its parts in the order they stand rather than as
 * what they are.
 *
 * <p>A declaration this program does not hold is refused. The program is closed over the
 * declarations its values can name, and this is where that is relied upon: answered as a
 * declaration with nothing under it, a value of one left out would be compared as whatever its
 * parts happen to look like.
 */
final class DeclaredFields implements Declarations {

    private final Map<TypeSymbol, Composed> byOwner;

    private DeclaredFields(Map<TypeSymbol, Composed> byOwner) {
        this.byOwner = byOwner;
    }

    /** Read off what each declaration is made of. */
    static Declarations over(List<CheckedData> declarations) {
        Map<TypeSymbol, Composed> byOwner = new LinkedHashMap<>();
        for (CheckedData each : declarations) {
            byOwner.put(each.name(), switch (each) {
                case CheckedData.Product product -> new Composed.OfFields(fieldsOf(product));
                // A sum is its cases and a unit carries nothing, so neither is a place a field
                // stands under.
                case CheckedData.Sum _, CheckedData.Unit _ -> Composed.NOTHING;
            });
        }
        return new DeclaredFields(byOwner);
    }

    private static Map<String, Type> fieldsOf(CheckedData.Product product) {
        Map<String, Type> fields = new LinkedHashMap<>();
        for (ValueShape.Field field : product.fields()) {
            fields.put(field.name(), field.type());
        }
        return fields;
    }

    @Override
    public Composed of(TypeSymbol.AtModule declared) {
        Composed composed = byOwner.get(declared);
        if (composed == null) {
            throw new IllegalStateException("`" + declared + "` is named by a value of this program"
                    + " and this program does not say what a value of it is made of");
        }
        return composed;
    }
}
