package souther.compiler.check;

import souther.compiler.ast.Ast;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.IdentityHashMap;
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
    /** Every module in this compilation, by name. The module being compiled is among them. */
    private final Map<String, Ast.Module> registry;
    /** What a bare name means here: this module's own definitions plus the imported ones. */
    private final Map<String, TypeName> scope;
    /** A qualifier a reference may carry → the module it names. Holds every module in the
     * compilation under its own name, plus each {@code import ... as} alias. */
    private final Map<String, String> qualifiers;
    /** Per-module definitions, built on first use so a module's own errors are still reported while
     * that module is being compiled rather than pulled forward into an unrelated one. */
    private final Map<String, Map<String, Ast.Def>> declared = new HashMap<>();
    /** Other modules' scopes, for names written in their declarations. Same reason to be lazy. */
    private final Map<String, Map<String, TypeName>> scopes = new HashMap<>();
    /** Other modules' qualifiers, since an {@code as} alias belongs to the module that wrote it. */
    private final Map<String, Map<String, String>> foreignQualifiers = new HashMap<>();
    /** Definition → declaring module, built on first use (see {@link #moduleOf}). */
    private IdentityHashMap<Ast.Def, String> homes;

    private Symbols(String module, Map<String, Ast.Module> registry,
                    Map<String, TypeName> scope, Map<String, String> qualifiers) {
        this.module = module;
        this.registry = registry;
        this.scope = scope;
        this.qualifiers = qualifiers;
    }

    /** No module at all — for signatures written over primitives and type variables only. */
    public static Symbols none() {
        return new Symbols("", Map.of(), Map.of(), Map.of());
    }

    /** A lone module, compiled with nothing else in sight: bare names are its own definitions. */
    public static Symbols of(Ast.Module m) {
        Map<String, TypeName> scope = new HashMap<>();
        for (String name : TypeChecker.ownDefs(m).keySet()) {
            scope.put(name, new TypeName(m.name(), name));
        }
        return new Symbols(m.name(), Map.of(m.name(), m), scope, Map.of(m.name(), m.name()));
    }

    /** A module compiled against a registry: {@code scope} is what its bare names mean (own plus
     * imported) and {@code aliases} maps each {@code import ... as} alias to its module. */
    public static Symbols of(Ast.Module m, Map<String, Ast.Module> registry,
                             Map<String, TypeName> scope, Map<String, String> aliases) {
        Map<String, String> qualifiers = new HashMap<>();
        for (String name : registry.keySet()) {
            qualifiers.put(name, name);
        }
        qualifiers.putAll(aliases);
        return new Symbols(m.name(), registry, scope, qualifiers);
    }

    /** The module being compiled. */
    public String module() {
        return module;
    }

    /** A name in the module being compiled. The caller vouches that it is declared here. */
    public TypeName own(String name) {
        return new TypeName(module, name);
    }

    /** The definition of {@code name}, or null when no module declares it. */
    public Ast.Def get(TypeName name) {
        return declaredIn(name.module()).get(name.name());
    }

    public boolean contains(TypeName name) {
        return get(name) != null;
    }

    /** The definition the written name {@code written} denotes here, or null when nothing does.
     * The name must have been written in the module being compiled — for one read out of another
     * module's declaration, resolve it there first ({@link #resolveIn}, {@link TypeName#sibling}). */
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

    /** Whether {@code name} is declared in another module (spec 4). */
    public boolean isForeign(TypeName name) {
        return !name.module().equals(module);
    }

    /** What the written name {@code written} denotes here, or null when nothing does. Accepts a bare
     * name, a module-qualified one ({@code probe.b.金額}) and an alias-qualified one ({@code B.金額}).
     * Visibility is enforced: a qualified name must be exposed by the module that declares it. */
    public TypeName resolve(String written) {
        return resolveIn(module, written);
    }

    /**
     * What {@code written} denotes where it was written — inside {@code inModule}. A name inside
     * another module's declaration (the element of a spread, a field's type) means what that module
     * says it means, not what the same spelling would mean here.
     */
    public TypeName resolveIn(String inModule, String written) {
        int dot = written.lastIndexOf('.');
        if (dot < 0) {
            return scopeOf(inModule).get(written);
        }
        String target = qualifiersOf(inModule).get(written.substring(0, dot));
        if (target == null) {
            return null;
        }
        TypeName candidate = new TypeName(target, written.substring(dot + 1));
        return contains(candidate) && exposes(target, candidate.name()) ? candidate : null;
    }

    /** The qualifiers a name written in {@code inModule} may carry: every module of this compilation
     * under its own name, plus that module's own {@code as} aliases — an alias is local to the module
     * that wrote it, so a name written there is read with its aliases, not this one's. */
    private Map<String, String> qualifiersOf(String inModule) {
        if (inModule.equals(module)) {
            return qualifiers;
        }
        Map<String, String> known = foreignQualifiers.get(inModule);
        if (known != null) {
            return known;
        }
        Map<String, String> built = new HashMap<>();
        for (String name : registry.keySet()) {
            built.put(name, name);
        }
        Ast.Module m = registry.get(inModule);
        if (m != null) {
            for (Ast.Import imp : m.imports()) {
                if (imp.alias() != null) {
                    built.put(imp.alias(), imp.module());
                }
            }
        }
        foreignQualifiers.put(inModule, built);
        return built;
    }

    /** What a bare name means in {@code inModule}: its own definitions plus what it imports. The
     * module being compiled has its scope built by the caller, with the import diagnostics; any other
     * module's is derived here, and an import it cannot satisfy is left out rather than reported —
     * that module's own compile is where such an import is answered for. */
    private Map<String, TypeName> scopeOf(String inModule) {
        if (inModule.equals(module)) {
            return scope;
        }
        Map<String, TypeName> known = scopes.get(inModule);
        if (known != null) {
            return known;
        }
        Map<String, TypeName> built = new HashMap<>();
        Ast.Module m = registry.get(inModule);
        if (m != null) {
            for (String name : declaredIn(inModule).keySet()) {
                built.put(name, new TypeName(inModule, name));
            }
            for (Ast.Import imp : m.imports()) {
                for (String name : imp.names()) {
                    TypeName imported = new TypeName(imp.module(), name);
                    if (contains(imported)) {
                        built.put(name, imported);
                    }
                }
            }
        }
        scopes.put(inModule, built);
        return built;
    }

    /** The module a qualifier names — a module of this compilation, or an import alias — or null
     * when it names none. Used to tell "unknown module" apart from "unknown type in a known
     * module". */
    public String moduleOfQualifier(String qualifier) {
        return qualifiers.get(qualifier);
    }

    /** Every qualifier a reference may carry here — what a "did you mean" may offer for one. */
    public Set<String> qualifiers() {
        return qualifiers.keySet();
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

    /**
     * The module that declares {@code def} — the module whose scope the names written inside it
     * (a spread, a field's type) are resolved in. Definitions are matched by identity, since two
     * modules may declare equal-looking ones. A definition the registry does not hold is one this
     * pass built for the module being compiled, so that is what it falls back to.
     */
    public String moduleOf(Ast.Def def) {
        if (homes == null) {
            homes = new IdentityHashMap<>();
            for (Ast.Module m : registry.values()) {
                for (Ast.Def d : m.defs()) {
                    homes.put(d, m.name());
                }
            }
        }
        return homes.getOrDefault(def, module);
    }

    /** Every definition of one module, keyed by the name written there. */
    public Map<String, Ast.Def> declaredIn(String moduleName) {
        Map<String, Ast.Def> defs = declared.get(moduleName);
        if (defs == null) {
            Ast.Module m = registry.get(moduleName);
            defs = m == null ? Map.of() : TypeChecker.ownDefs(m);
            declared.put(moduleName, defs);
        }
        return defs;
    }

    /** Whether {@code moduleName} exposes {@code name} (dropping any {@code .decoder} member). */
    private boolean exposes(String moduleName, String name) {
        if (moduleName.equals(module)) {
            return true;   // a module reaches its own definitions whether it exposes them or not
        }
        Ast.Module m = registry.get(moduleName);
        if (m == null) {
            return false;
        }
        for (String exposed : m.exposing()) {
            int dot = exposed.indexOf('.');
            if (name.equals(dot < 0 ? exposed : exposed.substring(0, dot))) {
                return true;
            }
        }
        return false;
    }
}
