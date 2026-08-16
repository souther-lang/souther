package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.types.Denotation;
import souther.compiler.types.TypeKey;

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;

/**
 * A {@link Scope} and a {@link Declarations} together, for the readers that have both to hand.
 *
 * <p>Not a thing of its own. It answers nothing itself except the one question that genuinely needs
 * both — {@link #reachable} takes the identities a bare name reaches here and asks what each is —
 * and hands over its two parts otherwise. The two answer different questions and fail in different ways:
 * a spelling nothing here writes is not a declaration that did not come out, and while one object
 * answered both, which of them a reader was holding was something it worked out for itself.
 */
public final class Symbols implements NameSense {

    private final TypeScope scope;
    private final Declarations<Hir.Def> declarations;

    private Symbols(String module, Registry<Hir.Def> registry,
                    Map<String, Denotation> names, Map<String, String> aliases) {
        this.scope = new TypeScope(module, names, aliases, registry);
        this.declarations = new Declarations<>(registry, Declarations.Vocabulary.ofLanguage());
    }

    /** No module at all — for signatures written over primitives and type variables only. */
    public static Symbols none() {
        return new Symbols("", Registry.empty(), Map.of(), Map.of());
    }

    /** A lone module, compiled with nothing else in sight: bare names are its own definitions. */
    public static Symbols of(Hir.Module m) {
        Map<String, Denotation> names = new HashMap<>();
        for (Hir.Def def : TypeChecker.ownDefs(m).values()) {
            names.put(def.name(), new Denotation.Denotes(def.declares()));
        }
        return new Symbols(m.name(), Registry.of(Map.of(m.name(), m)), names, Map.of());
    }

    /** A module compiled against a registry: {@code names} is what its bare names mean (own plus
     * imported) and {@code aliases} maps each {@code import ... as} alias to its module. */
    public static Symbols of(Hir.Module m, Map<String, Hir.Module> registry,
                             Map<String, Denotation> names, Map<String, String> aliases) {
        return of(m.name(), Registry.of(registry), names, aliases);
    }

    /** As {@link #of(Hir.Module, Map, Map, Map)}, over a registry that reads its declarations
     * however it likes — the form a query-backed compilation uses, where a module's definitions are
     * asked for one at a time rather than held in a map.
     *
     * <p>Reached through {@link Scoping.Scoped#symbolsOver}, for the reason
     * {@link SyntaxSymbols#of(String, Registry, Map, Map)} is. */
    static Symbols of(String module, Registry<Hir.Def> registry,
                      Map<String, Denotation> names, Map<String, String> aliases) {
        return new Symbols(module, registry, names, Map.copyOf(aliases));
    }

    /** What a name written here means. */
    @Override
    public TypeScope scope() {
        return scope;
    }

    /** What an identity is a declaration of. */
    public Declarations<Hir.Def> declarations() {
        return declarations;
    }

    @Override
    public boolean declares(TypeKey address) {
        return declarations.contains(address);
    }

    @Override
    public java.util.Set<String> declaredNamesIn(String module) {
        return declarations.declaredIn(module).keySet();
    }

    /** The module being compiled. */
    public String module() {
        return scope.module();
    }

    /**
     * Every bare spelling that reaches a definition here, and the definition it reaches — this
     * module\'s own plus the imported ones.
     *
     * <p>The one question that is both. What is reachable is the scope\'s to say and what each of
     * them is a declaration of is not, so this is written where both are to hand rather than in
     * either of them.
     *
     * <p>The pair and not either half. Which declaration a bare name denotes is what resolving it
     * answers, and a reader given only the declarations has to pair each back with a spelling of its
     * own — the same guess about which module declares what, made outside the only place that knows.
     * A spelling that reaches nothing is absent here and present in
     * {@code scope().namesInScope()}, those being two questions.
     */
    public Map<String, Hir.Def> reachable() {
        Map<String, Hir.Def> reached = new LinkedHashMap<>();
        scope.denotedNames().forEach((spelling, name) -> {
            Hir.Def def = declarations.declaration(name.key());
            if (def != null) {
                reached.put(spelling, def);
            }
        });
        return reached;
    }
}
