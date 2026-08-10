package souther.compiler.check;

import souther.compiler.Prelude;
import souther.compiler.ast.Ast;
import souther.compiler.types.TypeName;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * What a type name means in the module being compiled. It answers two different questions, and
 * keeping them apart is the point:
 *
 * <ul>
 *   <li><b>What does this written name refer to?</b> {@link #resolve} takes a name as the source
 *       wrote it — bare {@code 金額}, qualified {@code probe.b.金額}, or through an import alias —
 *       and yields the {@link TypeName} it denotes here. Only source text goes in.</li>
 *   <li><b>What is that type made of?</b> {@link #get} takes a {@link TypeName} and yields the
 *       definition, from whichever module declares it.</li>
 * </ul>
 *
 * <p>A name that came from another module's declaration (a sum's case list, say) must never be
 * resolved as if it had been written here — it is already anchored to its module, so it is reached
 * with {@link TypeName#sibling}.
 */
public final class Symbols {

    private final String module;
    /** Where the declarations of this compilation are read from. */
    private final Registry registry;
    /** What a bare name means here: this module's own definitions plus the imported ones. */
    private final Map<String, TypeName> scope;
    /** Each {@code import ... as} alias → the module it names. A module of the compilation is also
     * a qualifier under its own name, which {@link #moduleOfQualifier} reads off the registry
     * rather than listing here — listing it would mean naming every module up front. */
    private final Map<String, String> aliases;

    private Symbols(String module, Registry registry,
                    Map<String, TypeName> scope, Map<String, String> aliases) {
        this.module = module;
        this.registry = registry;
        this.scope = scope;
        this.aliases = aliases;
    }

    /** No module at all — for signatures written over primitives and type variables only. */
    public static Symbols none() {
        return new Symbols("", Registry.empty(), Map.of(), Map.of());
    }

    /** A lone module, compiled with nothing else in sight: bare names are its own definitions. */
    public static Symbols of(Ast.Module m) {
        Map<String, TypeName> scope = new HashMap<>();
        for (String name : TypeChecker.ownDefs(m).keySet()) {
            scope.put(name, new TypeName(m.name(), name));
        }
        return new Symbols(m.name(), Registry.of(Map.of(m.name(), m)), scope, Map.of());
    }

    /** A module compiled against a registry: {@code scope} is what its bare names mean (own plus
     * imported) and {@code aliases} maps each {@code import ... as} alias to its module. */
    public static Symbols of(Ast.Module m, Map<String, Ast.Module> registry,
                             Map<String, TypeName> scope, Map<String, String> aliases) {
        return of(m.name(), Registry.of(registry), scope, aliases);
    }

    /** As {@link #of(Ast.Module, Map, Map, Map)}, over a registry that reads its declarations
     * however it likes — the form a query-backed compilation uses, where a module's definitions are
     * asked for one at a time rather than held in a map. */
    public static Symbols of(String module, Registry registry,
                             Map<String, TypeName> scope, Map<String, String> aliases) {
        return new Symbols(module, registry, scope, Map.copyOf(aliases));
    }

    /** The module being compiled. */
    public String module() {
        return module;
    }

    /** A name in the module being compiled. The caller vouches that it is declared here. */
    public TypeName own(String name) {
        return new TypeName(module, name);
    }

    /** The definition of {@code name}, or null when no module declares it. The runtime namespace
     * declares the prelude's runtime-backed data ({@code RoundingMode}), which no module of the
     * compilation holds, so it is answered from the prelude's registration. */
    public Ast.Def get(TypeName name) {
        Ast.Def def = registry.declaration(name);
        return def != null ? def : Prelude.runtimeBackedDef(name);
    }

    public boolean contains(TypeName name) {
        return get(name) != null;
    }

    /** Whether {@code name} is declared by a module of this compilation — as opposed to a
     * declaration the language gives (the prelude's runtime-backed data), which resolves and types
     * like any other but belongs to no module here. The construction discipline asks this: what a
     * compilation declares is governed by {@code constructs}; the language's vocabulary is not. */
    public boolean declaredByCompilation(TypeName name) {
        return registry.declaration(name) != null;
    }

    /** The definition the written name {@code written} denotes here, or null when nothing does. The
     * name must have been written in the module being compiled. */
    public Ast.Def declaration(String written) {
        TypeName name = resolve(written);
        return name == null ? null : get(name);
    }

    /**
     * What a written case name denotes. Beside the data cases a module declares or imports, an arm may
     * name a case of a primitive-headed union: the primitive itself ({@code Int} in {@code Int |
     * DivisionByZero}), or one of the error cases the runtime declares rather than any module. Null
     * when it is none of those.
     */
    public TypeName resolveCase(String written) {
        return switch (written) {
            case "Int", "String", "Bool", "Decimal", "Date", "DateTime", "Raw" ->
                    TypeName.primitive(written);
            case "DivisionByZero", "NotANumber" -> TypeName.runtime(written);
            default -> resolve(written);
        };
    }

    /** Whether {@code name} is declared in another module (spec §modules). */
    public boolean isForeign(TypeName name) {
        return !name.module().equals(module);
    }

    /** What the written name {@code written} denotes here, or null when nothing does. Accepts a bare
     * name, a module-qualified one ({@code probe.b.金額}) and an alias-qualified one ({@code B.金額}).
     * Visibility is enforced: a qualified name must be exposed by the module that declares it.
     *
     * <p>"Here" is the whole story: a name is resolved in the module that wrote it, by that module's
     * own {@link Resolve} pass, so this never has to answer for a spelling written somewhere else.
     */
    public TypeName resolve(String written) {
        int dot = written.lastIndexOf('.');
        if (dot < 0) {
            TypeName name = scope.get(written);
            // The prelude's runtime-backed data is nameable everywhere, on the lowest rung: a
            // module's own declaration or import of the same name is what the name means there.
            return name != null ? name : Prelude.runtimeBackedType(written);
        }
        String target = moduleOfQualifier(written.substring(0, dot));
        if (target == null) {
            return null;
        }
        TypeName candidate = new TypeName(target, written.substring(dot + 1));
        return contains(candidate) && exposes(target, candidate.name()) ? candidate : null;
    }

    /**
     * The module of this compilation that exposes {@code name}, or null where that is not exactly
     * one module.
     *
     * <p>Asked where a bare name resolved to nothing, so that a name left off an import list is told
     * apart from a name nothing declares. This module is not among them: what it declares is already
     * in scope, so reaching here means it does not.
     *
     * <p>Exactly one, because the answer is written into a report as the module to reach for. Two
     * modules exposing the spelling makes naming either one a guess, and a guess in a hint is worse
     * than the silence it replaces — the reader is already being told the name is not in scope.
     */
    public String moduleExposing(String name) {
        String found = null;
        for (String other : new java.util.TreeSet<>(registry.moduleNames())) {
            if (other.equals(module) || !registry.exposedBy(other).contains(name)) {
                continue;
            }
            if (found != null) {
                return null;
            }
            found = other;
        }
        return found;
    }

    /** The module a qualifier names — a module of this compilation, or an import alias — or null
     * when it names none. Used to tell "unknown module" apart from "unknown type in a known
     * module". */
    public String moduleOfQualifier(String qualifier) {
        String alias = aliases.get(qualifier);
        if (alias != null) {
            return alias;
        }
        return registry.moduleNames().contains(qualifier) ? qualifier : null;
    }

    /** Every qualifier a reference may carry here — what a "did you mean" may offer for one. */
    public Set<String> qualifiers() {
        Set<String> all = new LinkedHashSet<>(registry.moduleNames());
        all.addAll(aliases.keySet());
        return all;
    }

    /** Whether {@code name} is reachable here as a bare name. */
    public boolean inScope(String name) {
        return scope.containsKey(name);
    }

    /** The bare names reachable here — what a "did you mean" suggestion may offer. */
    public Set<String> namesInScope() {
        return scope.keySet();
    }

    /** The definitions reachable here by a bare name: this module's own plus the imported ones. */
    public Collection<Ast.Def> visible() {
        List<Ast.Def> defs = new ArrayList<>();
        for (TypeName name : new LinkedHashSet<>(scope.values())) {
            Ast.Def def = get(name);
            if (def != null) {
                defs.add(def);
            }
        }
        return defs;
    }

    /** The names reachable here, canonical. */
    public Collection<TypeName> visibleNames() {
        return new LinkedHashSet<>(scope.values());
    }

    /** Every definition of one module, keyed by the name written there. The runtime namespace
     * answers with the prelude's runtime-backed data. */
    public Map<String, Ast.Def> declaredIn(String moduleName) {
        if (TypeName.RUNTIME.equals(moduleName)) {
            return Prelude.runtimeBackedDefs();
        }
        return registry.declaredIn(moduleName);
    }

    /** Whether the module that declares {@code name} exposes it — its own names always count. */
    public boolean isExposed(TypeName name) {
        return exposes(name.module(), name.name());
    }

    /** Whether {@code moduleName} exposes {@code name} (dropping any {@code .decoder} member). */
    private boolean exposes(String moduleName, String name) {
        if (moduleName.equals(module)) {
            return true;   // a module reaches its own definitions whether it exposes them or not
        }
        return registry.exposedBy(moduleName).contains(name);
    }
}
