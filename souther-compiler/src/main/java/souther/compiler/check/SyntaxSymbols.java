package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.types.Denotation;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeName;
import souther.compiler.types.TypeSymbols;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

/**
 * What {@code Resolve} reads a module against: what a name written here means, and the declarations
 * of this compilation as they were written.
 *
 * <p>The counterpart of {@link Symbols}, one representation earlier. The scope is the same object —
 * what a spelling denotes is decided from the names in sight and not from any tree — and the
 * declarations are not: a module {@code Resolve} is resolving against has not been resolved itself,
 * because a name written there is that module's to answer and asking for its resolved form here
 * would be this module waiting on its own.
 *
 * <p>Which is why the two are separate types rather than one holding a stage. There is one reader at
 * this representation and everything else is at the other, so a reader that is handed one of these
 * cannot ask a question only the resolved declarations can answer.
 */
public final class SyntaxSymbols implements NameSense {

    private final TypeScope scope;
    private final Declarations<Ast.Def> declarations;

    private SyntaxSymbols(String module, Registry<Ast.Def> registry,
                          Map<String, Denotation> names, Map<String, String> aliases) {
        this.scope = new TypeScope(module, names, aliases, registry);
        this.declarations = new Declarations<>(registry, Declarations.Vocabulary.ofNothing());
    }

    /** No module at all — for signatures written over primitives and type variables only. */
    public static SyntaxSymbols none() {
        return new SyntaxSymbols("", Registry.ofWritten(Map.of()), Map.of(), Map.of());
    }

    /** A lone module, resolved with nothing else in sight: bare names are its own definitions. */
    public static SyntaxSymbols of(Ast.Module m) {
        Map<String, Denotation> names = new HashMap<>();
        for (Ast.Def def : Registry.ownDefs(m).values()) {
            names.put(def.name(),
                    new Denotation.Denotes(TypeSymbols.declared(def.declaredKey())));
        }
        return new SyntaxSymbols(m.name(), Registry.ofWritten(Map.of(m.name(), m)), names, Map.of());
    }

    /** A module resolved against a registry that reads its declarations however it likes — the form
     * a query-backed compilation uses. */
    public static SyntaxSymbols of(String module, Registry<Ast.Def> registry,
                                   Map<String, Denotation> names, Map<String, String> aliases) {
        return new SyntaxSymbols(module, registry, names, Map.copyOf(aliases));
    }

    /** What a name written here means. */
    @Override
    public TypeScope scope() {
        return scope;
    }

    /** What an identity is a declaration of, as it was written. */
    public Declarations<Ast.Def> declarations() {
        return declarations;
    }

    /** The module being resolved. */
    public String module() {
        return scope.module();
    }

    @Override
    public boolean declares(TypeKey address) {
        return declarations.contains(address);
    }

    @Override
    public Set<String> declaredNamesIn(String module) {
        return declarations.declaredIn(module).keySet();
    }
}
