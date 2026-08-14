package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.ast.Hir;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

/**
 * Where the declarations of a compilation are read from. {@link Symbols} answers what a name means
 * here; this answers what any module declares, which is the part that is not about "here" at all.
 *
 * <p>Three questions, and no more: a module's definitions, what it exposes, and which modules there
 * are. Keeping it to that is the point — a registry that handed out {@code Hir.Module} would let a
 * caller reach a module's behaviors, examples or fns and so depend on which pass had last rewritten
 * it, which is how a definition's meaning came to depend on the whole compile.
 */
public interface Registry<D> {

    /**
     * One declaration, or null when no module of this compilation declares it.
     *
     * <p>The question nearly everything asks, and the reason it is not {@link #declaredIn}: reading
     * a whole module's declarations to reach one of them makes the reader depend on all of them, so
     * declaring something new — which nobody can even see yet — reaches every module that imported
     * anything from there.
     */
    D declaration(TypeKey address);

    /**
     * The identity of the declaration that address names, or null where nothing declares it.
     *
     * <p>Asking rather than assembling. A reader with a module and a name has an address, and an
     * address is not an identity until something declares one there — so this is where the two are
     * told apart, and a reader that gets nothing back has nothing it could have gone on with.
     */
    default TypeSymbol identify(TypeKey address) {
        return declaration(address) != null ? TypeSymbols.declared(address) : null;
    }

    /** Every definition of one module, keyed by the name written there. Empty when this compilation
     * has no such module.
     *
     * <p>For the questions that really are about a whole module — which sum a case belongs to, what
     * a "did you mean" may offer. A reader after one declaration asks {@link #declaration}. */
    Map<String, D> declaredIn(String moduleName);

    /** The base type names {@code moduleName} exposes, with any {@code .decoder} / {@code .encoder}
     * member dropped. Empty when this compilation has no such module. */
    Set<String> exposedBy(String moduleName);

    /** Every module name in this compilation. A qualifier is one of these or an import alias. */
    Set<String> moduleNames();

    /** Nothing is declared anywhere — for signatures written over primitives and type variables. */
    static Registry<Hir.Def> empty() {
        return of(Map.of());
    }

    /** The declarations of a fixed set of modules. Each module's definitions are worked out on
     * first use, so a compilation that never reaches a module never reads it. */
    static Registry<Hir.Def> of(Map<String, Hir.Module> modules) {
        return new Registry<Hir.Def>() {
            private final Map<String, Map<String, Hir.Def>> defs = new HashMap<>();
            private final Map<String, Set<String>> exposed = new HashMap<>();

            @Override
            public Hir.Def declaration(TypeKey address) {
                return declaredIn(address.module()).get(address.name());
            }

            @Override
            public Map<String, Hir.Def> declaredIn(String moduleName) {
                return defs.computeIfAbsent(moduleName, name -> {
                    Hir.Module m = modules.get(name);
                    return m == null ? Map.of() : TypeChecker.ownDefs(m);
                });
            }

            @Override
            public Set<String> exposedBy(String moduleName) {
                return exposed.computeIfAbsent(moduleName, name -> {
                    Hir.Module m = modules.get(name);
                    return m == null ? Set.of() : baseNames(m.exposing());
                });
            }

            @Override
            public Set<String> moduleNames() {
                return modules.keySet();
            }
        };
    }

    /** A module's own definitions as it wrote them, keyed by the name written there. */
    static Map<String, Ast.Def> ownDefs(Ast.Module module) {
        DeclaredNames.Of<Ast.Def> declared = DeclaredNames.of(module.defs(), Ast.Def::name,
                Ast.Def::written, Ast.Def::pos);
        if (!declared.rejected().isEmpty()) {
            throw declared.rejected().get(0);
        }
        return declared.defs();
    }

    /** The declarations of a fixed set of modules, as they were written — what {@code Resolve}
     * reads other modules by. */
    static Registry<Ast.Def> ofWritten(Map<String, Ast.Module> modules) {
        return new Registry<Ast.Def>() {
            private final Map<String, Map<String, Ast.Def>> defs = new HashMap<>();

            @Override
            public Ast.Def declaration(TypeKey address) {
                return declaredIn(address.module()).get(address.name());
            }

            @Override
            public Map<String, Ast.Def> declaredIn(String moduleName) {
                return defs.computeIfAbsent(moduleName, name -> {
                    Ast.Module m = modules.get(name);
                    return m == null ? Map.of() : ownDefs(m);
                });
            }

            @Override
            public Set<String> exposedBy(String moduleName) {
                Ast.Module m = modules.get(moduleName);
                return m == null ? Set.of() : baseNames(m.exposing());
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
