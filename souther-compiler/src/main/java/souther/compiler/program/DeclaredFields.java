package souther.compiler.program;

import souther.compiler.core.ValueShape;
import souther.compiler.observe.Position;
import souther.compiler.observe.ValueTypes;
import souther.compiler.types.TypeSymbol;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * What this program's declarations say stands at each place inside a value.
 *
 * <p>The one question a comparison asks of the declarations, answered from the declarations this
 * program publishes and from nothing else. So a row read against an answer here is read against
 * exactly what a reader of {@link CheckedProgram#declaration} would lay a value out by, and the two
 * cannot come apart.
 *
 * <p>Over every declaration this compile resolved, its own modules' and the language's and a
 * dependency's alike: a value stated for one module's behavior may hold a value of another's, and a
 * comparison that could not read the second would read its elements in the order they stand rather
 * than as what they are.
 *
 * <p>What nothing declares is {@link Position#UNREAD}, which is an answer and not a failure. A
 * comparison meets it where a value states a field its type does not declare — a disagreement it
 * reports as one — and reading it as an absent declaration is what says nothing is written beside
 * the value there.
 */
final class DeclaredFields implements ValueTypes {

    private final Map<TypeSymbol, Map<String, Position>> byOwner;

    private DeclaredFields(Map<TypeSymbol, Map<String, Position>> byOwner) {
        this.byOwner = byOwner;
    }

    /** Read off what each declaration is made of. A sum and a unit have no fields, so neither is
     *  a place a field stands under. */
    static ValueTypes over(List<CheckedData> declarations) {
        Map<TypeSymbol, Map<String, Position>> byOwner = new LinkedHashMap<>();
        for (CheckedData declared : declarations) {
            if (!(declared instanceof CheckedData.Product product)) {
                continue;
            }
            Map<String, Position> fields = new LinkedHashMap<>();
            for (ValueShape.Field field : product.fields()) {
                fields.put(field.name(), Position.at(field.type()));
            }
            byOwner.put(declared.name(), fields);
        }
        return new DeclaredFields(byOwner);
    }

    @Override
    public Position field(TypeSymbol owner, String field) {
        return byOwner.getOrDefault(owner, Map.of()).getOrDefault(field, Position.UNREAD);
    }
}
