package souther.compiler.program;

import souther.compiler.core.ValueShape;
import souther.compiler.observe.FieldTypes;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * What this program's declarations say each field of a value holds.
 *
 * <p>The one question a reader of a value's parts asks of the declarations, answered from the
 * declarations this program publishes and from nothing else. So a row read against an answer here is
 * read against exactly what a reader of {@link CheckedProgram#declaration} would lay a value out by,
 * and the two cannot come apart.
 *
 * <p>Over every declaration this compile resolved, its own modules' and the language's and a
 * dependency's alike: a value stated for one module's behavior may hold a value of another's, and a
 * reader that could not read the second would read its elements in the order they stand rather than
 * as what they are.
 *
 * <p>A data with no fields to take — a sum, a unit — has none, which is an answer. A declaration
 * this program does not hold at all is not: a value naming one is a value this program cannot lay
 * out, and answering that it has no such field would let a row about it be compared as whatever its
 * parts happen to look like. The program is closed over the declarations its values can name, and
 * this is where that is relied upon.
 */
final class DeclaredFields implements FieldTypes {

    private final Map<TypeSymbol, Map<String, Type>> byOwner;
    private final Set<TypeSymbol> declared;

    private DeclaredFields(Map<TypeSymbol, Map<String, Type>> byOwner, Set<TypeSymbol> declared) {
        this.byOwner = byOwner;
        this.declared = declared;
    }

    /** Read off what each declaration is made of. A sum and a unit have no fields, so neither is
     *  a place a field stands under. */
    static FieldTypes over(List<CheckedData> declarations) {
        Map<TypeSymbol, Map<String, Type>> byOwner = new LinkedHashMap<>();
        Set<TypeSymbol> declared = new LinkedHashSet<>();
        for (CheckedData each : declarations) {
            declared.add(each.name());
            if (each instanceof CheckedData.Product product) {
                Map<String, Type> fields = new LinkedHashMap<>();
                for (ValueShape.Field field : product.fields()) {
                    fields.put(field.name(), field.type());
                }
                byOwner.put(each.name(), fields);
            }
        }
        return new DeclaredFields(byOwner, declared);
    }

    @Override
    public Map<String, Type> of(TypeSymbol owner) {
        Map<String, Type> fields = byOwner.get(owner);
        if (fields != null) {
            return fields;
        }
        // What the language gives is a primitive or a case it declares no fields for, and no module
        // wrote it: there is nothing here that could have been left out.
        if (owner instanceof TypeSymbol.AtModule && !declared.contains(owner)) {
            throw new IllegalStateException("`" + owner + "` is named by a value of this program and"
                    + " this program does not say what a value of it is made of");
        }
        return Map.of();
    }
}
