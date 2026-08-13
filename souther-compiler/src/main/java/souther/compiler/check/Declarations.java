package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.types.TypeName;

import java.util.Map;

/**
 * What a semantic identity is a declaration of.
 *
 * <p>The other half of what a module needs, and not the half {@link Scope} answers: this takes an
 * identity and never a spelling, so nothing here has to know which module is being compiled. A
 * reader holding one of these has already resolved whatever it is asking about.
 *
 * <p>Two sources, kept apart. {@link Registry} is what this compilation declares, read one
 * declaration at a time; the language's own vocabulary — the prelude's runtime-backed data — is
 * declared by no module of the compilation and is answered beside it. {@link #declaration} sees
 * both, because a name that denotes one types like a name that denotes the other;
 * {@link #declaredByCompilation} sees only the first, because what a compilation may construct is
 * governed by {@code constructs} and the language's vocabulary is not.
 *
 * <p>Asked one identity at a time. {@link #declaredIn} enumerates, for the questions that really are
 * about a whole module — which sum a case belongs to, what a "did you mean" may offer — and is not
 * how {@link #declaration} is answered. Reading a module's declarations to reach one of them makes
 * the reader depend on all of them, and the failure of any one of them becomes the failure of every
 * question about the rest.
 */
public final class Declarations {

    private final Registry registry;

    Declarations(Registry registry) {
        this.registry = registry;
    }

    /** The declaration {@code name} names, or null when nothing declares it. */
    public Ast.Def declaration(TypeName name) {
        Ast.Def def = registry.declaration(name);
        return def != null ? def : Prelude.runtimeBackedDef(name);
    }

    /** Whether anything declares {@code name} — this compilation or the language. */
    public boolean contains(TypeName name) {
        return declaration(name) != null;
    }

    /** Whether {@code name} is declared by a module of this compilation — as opposed to a
     * declaration the language gives (the prelude's runtime-backed data), which resolves and types
     * like any other but belongs to no module here. The construction discipline asks this: what a
     * compilation declares is governed by {@code constructs}; the language's vocabulary is not. */
    public boolean declaredByCompilation(TypeName name) {
        return registry.declaration(name) != null;
    }

    /** Every definition of one module, keyed by the name written there. The runtime namespace
     * answers with the prelude's runtime-backed data. */
    public Map<String, Ast.Def> declaredIn(String moduleName) {
        if (TypeName.RUNTIME.equals(moduleName)) {
            return Prelude.runtimeBackedDefs();
        }
        return registry.declaredIn(moduleName);
    }
}
