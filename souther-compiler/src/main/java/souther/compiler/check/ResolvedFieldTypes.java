package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.observe.FieldTypes;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * What the declarations a text has resolved so far say its fields hold.
 *
 * <p>The reading for a program that has not been accepted: an editor asks what may be written after
 * a {@code .} while the module around it is still being typed, and what it can be told is what the
 * declarations denote at this revision. Nothing here is a decision of the check's, and nothing here
 * waits for one — a declaration whose clause does not elaborate still has fields, and an author
 * reading its name deserves them.
 *
 * <p>Not the reading a checked program is compared against. What a value of an accepted declaration
 * is made of is what the check settled, and a reader in that world takes it from there; this one is
 * handed to readers whose world has no such answer, so that neither of them has to decide what to
 * do when it is missing.
 *
 * <p>A written type this cannot read as a reference to a declaration is a field this says nothing
 * about. It denotes something — a function type denotes a function — but what it denotes is not a
 * place a value crosses a boundary at, and a declaration writing one is refused before it is ever
 * accepted.
 */
public final class ResolvedFieldTypes implements FieldTypes {

    private final Symbols symbols;

    public ResolvedFieldTypes(Symbols symbols) {
        if (symbols == null) {
            throw new IllegalArgumentException("what a declaration denotes is read against a world");
        }
        this.symbols = symbols;
    }

    @Override
    public Map<String, Type> of(TypeSymbol owner) {
        Map<String, Type> out = new LinkedHashMap<>();
        written(owner, symbols).forEach((field, declared) -> {
            Type is = declared.denotes();
            if (is != null) {
                out.put(field, is);
            }
        });
        return out;
    }

    /**
     * A data's fields as they are written, following the {@code ...includes} it composes in (spec
     * §data).
     *
     * <p>A spread naming nothing brings in no fields, and a name repeated between two of them keeps
     * the one reached first: both are refused where the declaration is checked, and this reading is
     * for a text where that check has not run.
     */
    static Map<String, Hir.TypeRef> written(TypeSymbol typeName, Symbols symbols) {
        Map<String, Hir.TypeRef> out = new LinkedHashMap<>();
        if (symbols.declarations().declaration(typeName) instanceof Hir.Data d) {
            for (Hir.Name inc : d.includes()) {
                if (inc.answered() instanceof Hir.Name.Denoting named) {
                    out.putAll(written(named.type(), symbols));
                }
            }
            for (Hir.Field f : d.fields()) {
                if (f.type() instanceof Hir.TypeRef ref) {
                    out.put(f.name(), ref);
                }
            }
        }
        return out;
    }
}
