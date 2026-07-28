package souther.compiler.check;

import souther.compiler.ast.Ast;

import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

/**
 * Where the declarations of a compilation are read from. {@link Symbols} answers what a name means
 * here; this answers what any module declares, which is the part that is not about "here" at all.
 *
 * <p>Three questions, and no more: a module's definitions, what it exposes, and which modules there
 * are. Keeping it to that is the point — a registry that handed out {@code Ast.Module} would let a
 * caller reach a module's behaviors, examples or fns and so depend on which pass had last rewritten
 * it, which is how a definition's meaning came to depend on the whole compile.
 */
public interface Registry {

    /** Every definition of one module, keyed by the name written there. Empty when this compilation
     * has no such module. */
    Map<String, Ast.Def> declaredIn(String moduleName);

    /** The base type names {@code moduleName} exposes, with any {@code .decoder} / {@code .encoder}
     * member dropped. Empty when this compilation has no such module. */
    Set<String> exposedBy(String moduleName);

    /** Every module name in this compilation. A qualifier is one of these or an import alias. */
    Set<String> moduleNames();

    /** Nothing is declared anywhere — for signatures written over primitives and type variables. */
    static Registry empty() {
        return of(Map.of());
    }

    /** The declarations of a fixed set of modules. Each module's definitions are worked out on
     * first use, so a compilation that never reaches a module never reads it. */
    static Registry of(Map<String, Ast.Module> modules) {
        return new Registry() {
            private final Map<String, Map<String, Ast.Def>> defs = new HashMap<>();
            private final Map<String, Set<String>> exposed = new HashMap<>();

            @Override
            public Map<String, Ast.Def> declaredIn(String moduleName) {
                return defs.computeIfAbsent(moduleName, name -> {
                    Ast.Module m = modules.get(name);
                    return m == null ? Map.of() : TypeChecker.ownDefs(m);
                });
            }

            @Override
            public Set<String> exposedBy(String moduleName) {
                return exposed.computeIfAbsent(moduleName, name -> {
                    Ast.Module m = modules.get(name);
                    return m == null ? Set.of() : baseNames(m.exposing());
                });
            }

            @Override
            public Set<String> moduleNames() {
                return modules.keySet();
            }
        };
    }

    /** An {@code exposing} list as the type names it names: {@code Amount.decoder} exposes
     * {@code Amount}. */
    static Set<String> baseNames(Iterable<String> exposing) {
        Set<String> names = new LinkedHashSet<>();
        for (String e : exposing) {
            int dot = e.indexOf('.');
            names.add(dot < 0 ? e : e.substring(0, dot));
        }
        return Set.copyOf(names);
    }
}
