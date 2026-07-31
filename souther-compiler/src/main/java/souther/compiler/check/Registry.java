package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.types.TypeName;

import java.util.HashMap;
import java.util.Optional;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicReference;

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

    /**
     * One declaration, or null when no module of this compilation declares it.
     *
     * <p>The question nearly everything asks, and the reason it is not {@link #declaredIn}: reading
     * a whole module's declarations to reach one of them makes the reader depend on all of them, so
     * declaring something new — which nobody can even see yet — reaches every module that imported
     * anything from there.
     */
    Ast.Def declaration(TypeName name);

    /** Every definition of one module, keyed by the name written there. Empty when this compilation
     * has no such module.
     *
     * <p>For the questions that really are about a whole module — which sum a case belongs to, what
     * a "did you mean" may offer. A reader after one declaration asks {@link #declaration}. */
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
            public Ast.Def declaration(TypeName name) {
                return declaredIn(name.module()).get(name.name());
            }

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

    /**
     * The same declarations, each read once and then kept, and safe to read from more than one
     * thread.
     *
     * <p>For a reader that runs code — evaluating a module's example rows — rather than for the
     * compiler's own passes. A query-backed registry reads the store the compilation is being
     * answered from, and that store is single-threaded; evaluating rows at the same time would have
     * several of them asking it at once. Here every answer after the first comes from this map
     * without reaching the store at all, and the few that do go one at a time.
     *
     * <p>Holding the answers is sound because the reader is inside one question: the declarations
     * cannot change while it is being answered, and when something does change, this registry is
     * built again along with the answer that reads it.
     */
    static Registry cached(Registry of) {
        return new Registry() {
            private final Map<TypeName, Optional<Ast.Def>> declarations = new ConcurrentHashMap<>();
            private final Map<String, Map<String, Ast.Def>> inModule = new ConcurrentHashMap<>();
            private final Map<String, Set<String>> exposed = new ConcurrentHashMap<>();
            private final AtomicReference<Set<String>> modules = new AtomicReference<>();

            @Override
            public Ast.Def declaration(TypeName name) {
                Optional<Ast.Def> known = declarations.get(name);
                if (known == null) {
                    synchronized (this) {
                        known = declarations.get(name);
                        if (known == null) {
                            known = Optional.ofNullable(of.declaration(name));
                            declarations.put(name, known);
                        }
                    }
                }
                return known.orElse(null);
            }

            @Override
            public Map<String, Ast.Def> declaredIn(String moduleName) {
                Map<String, Ast.Def> known = inModule.get(moduleName);
                if (known == null) {
                    synchronized (this) {
                        known = inModule.computeIfAbsent(moduleName, of::declaredIn);
                    }
                }
                return known;
            }

            @Override
            public Set<String> exposedBy(String moduleName) {
                Set<String> known = exposed.get(moduleName);
                if (known == null) {
                    synchronized (this) {
                        known = exposed.computeIfAbsent(moduleName, of::exposedBy);
                    }
                }
                return known;
            }

            @Override
            public Set<String> moduleNames() {
                Set<String> known = modules.get();
                if (known == null) {
                    synchronized (this) {
                        known = modules.get();
                        if (known == null) {
                            known = of.moduleNames();
                            modules.set(known);
                        }
                    }
                }
                return known;
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
