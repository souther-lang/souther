package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.core.Kernel;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.diag.CompileException;
import souther.compiler.types.Denotation;
import souther.compiler.types.TypeKey;
import souther.compiler.types.ValueName;

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
    /** The library this module is compiled against. Held so that a reader already holding the
     *  symbol table has it — what a library operation is declared to be is part of what names mean
     *  here, and a reader that fetched its own could be reading a different library from the one
     *  this module's names were resolved against. */
    private final Stdlib stdlib;

    private Symbols(String module, Registry<Hir.Def> registry, Denoting names, Stdlib stdlib) {
        this.scope = new TypeScope(module, names, registry,
                stdlib.names().languageTypes());
        this.declarations = new Declarations<>(registry, Declarations.Vocabulary.of(stdlib));
        this.stdlib = stdlib;
    }

    /** No module at all — for signatures written over primitives and type variables only. The
     *  library still arrives, because a signature over primitives may still name a library
     *  operation, and a caller with none of its own has one to hand. */
    public static Symbols none(Stdlib stdlib) {
        return new Symbols("", Registry.empty(), Denoting.NONE, stdlib);
    }

    /**
     * The one walk the library publishes, which an output lowers as a loop rather than as a call.
     *
     * <p>Handed on rather than looked up. An output holds these symbols already and this is one
     * value of the language it was compiled against, so asking here is asking what it was given —
     * where reaching {@link #library()} would be an output that could put any question to the
     * library, which {@code TheBackendEmitsAgainstTheLanguageItWasHanded} keeps closed.
     */
    public ValueName.Stdlib.Operation theWalk() {
        return stdlib.theWalk();
    }

    /**
     * The one operation the library publishes that states elements are distinct, which an invariant
     * written over is a constraint rather than a call.
     *
     * <p>Handed on for the reason {@link #theWalk} is.
     */
    public ValueName.Stdlib.Operation theDistinctnessPredicate() {
        return stdlib.theDistinctnessPredicate();
    }

    /**
     * Which kernel {@code operation} is declared to be, or null where it is not a kernel.
     *
     * <p>The question a pass asks when it recognises an operation by what it does rather than by
     * what it is called: a kernel is the language's own vocabulary and is the same whatever alias a
     * library publishes the operation under. Answered here rather than by reaching
     * {@link #library()} so that a reader holding these symbols has it — a {@code Kernel} is
     * {@code core}'s, so an output asking this is not naming the library.
     */
    public Kernel kernelOf(ValueName.Stdlib.Operation operation) {
        Stdlib.Intrinsic intrinsic = stdlib.intrinsicOf(operation);
        return intrinsic == null ? null : intrinsic.kernel();
    }

    /** The library this module is compiled against. */
    public Stdlib library() {
        return stdlib;
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
    public static Symbols of(Hir.Module m, Stdlib stdlib) {
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
                Denoting.of(names, Map.of()), stdlib);
    }

    /** A module compiled over a registry that reads its declarations
     * however it likes — the form a query-backed compilation uses, where a module's definitions are
     * asked for one at a time rather than held in a map.
     *
     * <p>What names mean here arrives as a {@link Denoting} rather than as the table itself, for
     * the reason that interface gives: a reader that fetched the table to build this would have
     * depended on every name in the module before reading one of them. The three that are one
     * assembly — the module, its meanings and its aliases — still arrive together, because a caller
     * free to pair them itself could pair parts of two. */
    public static Symbols of(String module, Registry<Hir.Def> registry, Denoting names,
                             Stdlib stdlib) {
        return new Symbols(module, registry, names, stdlib);
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
            Hir.Def def = declarations.declaration(name);
            if (def != null) {
                reached.put(spelling, def);
            }
        });
        return reached;
    }
}
