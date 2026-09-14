package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.core.Kernel;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.diag.CompileException;
import souther.compiler.types.Denotation;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

/**
 * Names and declarations as resolution left them.
 *
 * <p>One of the two declaration worlds. What a reader gets from {@link #declarations} here is
 * {@link Hir.Def}, which is what a pass above the derivation has and all it has: nothing has
 * answered for a declaration's boundary representation yet, and there is no state in which one of
 * these carries one.
 */
public final class ResolvedSymbols implements Symbols {

    private final SymbolTable<Hir.Def> table;

    private ResolvedSymbols(SymbolTable<Hir.Def> table) {
        this.table = table;
    }

    /** No module at all — for signatures written over primitives and type variables only. */
    static ResolvedSymbols none(Stdlib stdlib) {
        return new ResolvedSymbols(new SymbolTable<>("", Registry.empty(), Denoting.NONE,
                Declarations.Vocabulary.of(stdlib), stdlib, each -> each));
    }

    /**
     * A lone module, compiled with nothing else in sight: bare names are its own definitions.
     *
     * <p>Indexed here, so that what comes back is a symbol table over declarations this module has,
     * and refused here where it may not have one. Refused as the report and not as a fault: a module
     * of this compilation reaches this stage carrying a declaration it may not have, because
     * {@code Names} reports that one and goes on with the rest, and resolution resolves the module
     * as it was written. So the author holds the file, and what to do about it is the same thing
     * {@link SyntaxSymbols#of(souther.compiler.ast.Ast.Module, Stdlib)} says one representation
     * earlier.
     */
    static ResolvedSymbols of(Hir.Module m, Stdlib stdlib) {
        DeclaredNames.Index<Hir.Def> declared = Registry.indexed(m);
        if (!declared.refusals().isEmpty()) {
            throw CompileException.of(
                    DeclarationRefusals.reportedAsResolved(declared.refusals().get(0)));
        }
        Map<String, Denotation> names = new HashMap<>();
        for (Hir.Def def : declared.declarations().values()) {
            names.put(def.name(), new Denotation.Denotes(def.declares()));
        }
        return new ResolvedSymbols(new SymbolTable<>(m.name(),
                Registry.ofRead(Map.of(m.name(), new Registry.Declared<>(
                        declared.declarations(), Registry.baseNames(m.exposing())))),
                Denoting.of(names, Map.of()), Declarations.Vocabulary.of(stdlib), stdlib,
                each -> each));
    }

    /** A module compiled over a registry that reads its declarations however it likes — the form a
     * query-backed compilation uses, where a module's definitions are asked for one at a time rather
     * than held in a map.
     *
     * <p>What names mean here arrives as a {@link Denoting} rather than as the table itself, for
     * the reason that interface gives: a reader that fetched the table to build this would have
     * depended on every name in the module before reading one of them. The three that are one
     * assembly — the module, its meanings and its aliases — still arrive together, because a caller
     * free to pair them itself could pair parts of two. */
    public static ResolvedSymbols over(String module, Registry<Hir.Def> registry, Denoting names,
                                       Stdlib stdlib) {
        return new ResolvedSymbols(new SymbolTable<>(module, registry, names,
                Declarations.Vocabulary.of(stdlib), stdlib, each -> each));
    }

    /**
     * What an identity is a declaration of, as resolution left it.
     *
     * <p>Reached by naming this world. A reader that took the table off {@link Symbols} would be
     * reading declarations at whichever stage it happened to be handed, which is what having two
     * carriers is for.
     */
    public Declarations<Hir.Def> declarations() {
        return table.declarations();
    }

    /**
     * Every bare spelling that reaches a definition here, and the definition it reaches — this
     * module's own plus the imported ones.
     *
     * <p>The one question that is both. What is reachable is the scope's to say and what each of
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
        return table.reachable(table.scope());
    }

    @Override
    public TypeScope scope() {
        return table.scope();
    }

    @Override
    public Hir.Def declaredNode(TypeSymbol name) {
        return table.declaredNode(name);
    }

    @Override
    public Hir.Def declaredNode(TypeKey address) {
        return table.declaredNode(address);
    }

    @Override
    public boolean declares(TypeKey address) {
        return table.declares(address);
    }

    @Override
    public boolean declaredByCompilation(TypeSymbol name) {
        return table.declaredByCompilation(name);
    }

    @Override
    public boolean declaredByCompilation(TypeKey address) {
        return table.declaredByCompilation(address);
    }

    @Override
    public Set<String> declaredNamesIn(String module) {
        return table.declaredNamesIn(module);
    }

    @Override
    public String module() {
        return table.module();
    }

    @Override
    public Stdlib library() {
        return table.library();
    }

    @Override
    public ValueName.Stdlib.Operation theWalk() {
        return table.theWalk();
    }

    @Override
    public ValueName.Stdlib.Operation theDistinctnessPredicate() {
        return table.theDistinctnessPredicate();
    }

    @Override
    public Kernel kernelOf(ValueName.Stdlib.Operation operation) {
        return table.kernelOf(operation);
    }
}
