package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.diag.CompileException;
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

    /**
     * A lone module, compiled with nothing else in sight: bare names are its own definitions.
     *
     * <p>Indexed here, so that what comes back is a symbol table over declarations this module has,
     * and refused here where it may not have one. Refused as the report and not as a fault: a module
     * of this compilation reaches this stage carrying a declaration it may not have, because
     * {@code Names} reports that one and goes on with the rest, and resolution resolves the module
     * as it was written. So the author holds the file, and what to do about it is the same thing
     * {@link SyntaxSymbols#of(souther.compiler.ast.Ast.Module)} says one representation earlier.
     */
    public static Symbols of(Hir.Module m) {
        DeclaredNames.Index<Hir.Def> declared = Registry.indexed(m);
        if (!declared.refusals().isEmpty()) {
            throw CompileException.of(
                    DeclarationRefusals.reportedAsResolved(declared.refusals().get(0)));
        }
        Map<String, Denotation> names = new HashMap<>();
        for (Hir.Def def : declared.declarations().values()) {
            names.put(def.name(), new Denotation.Denotes(def.declares()));
        }
        return new Symbols(m.name(),
                Registry.ofRead(Map.of(m.name(), new Registry.Declared<>(
                        declared.declarations(), Registry.baseNames(m.exposing())))),
                names, Map.of());
    }

    /** A module compiled over a registry that reads its declarations
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
