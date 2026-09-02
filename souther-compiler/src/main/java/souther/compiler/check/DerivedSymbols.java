package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.core.Kernel;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.util.Map;
import java.util.Set;

/**
 * Names and declarations as the derivation answered for them.
 *
 * <p>The other declaration world. What {@link #declarations} hands over is {@link Derived.Def}, so a
 * reader that names this type is one that has to be below the derivation — and one that needs what
 * the derivation established about a declaration has nowhere else to ask.
 *
 * <p>Both sources it answers from are at this rung. The compilation's declarations come from the
 * derived registry, and the language's own vocabulary is lifted to the same representation
 * ({@link Declarations.Vocabulary#ofDerived}) rather than left at the one below it, which is what
 * used to make a table of nodes the only thing the two could be read through.
 */
public final class DerivedSymbols implements Symbols {

    private final SymbolTable<Derived.Def> table;

    private DerivedSymbols(SymbolTable<Derived.Def> table) {
        this.table = table;
    }

    /** A module over a registry of derived declarations, with the language's vocabulary lifted to
     * the same rung. */
    public static DerivedSymbols over(String module, Registry<Derived.Def> registry, Denoting names,
                                      Stdlib stdlib) {
        return new DerivedSymbols(new SymbolTable<>(module, registry, names,
                Declarations.Vocabulary.ofDerived(stdlib), stdlib));
    }

    /**
     * What an identity is a declaration of, as the derivation answered for it.
     *
     * <p>Reached by naming this world and by nothing else. There is no operation anywhere that turns
     * what this holds into a table of {@link Hir.Def}: a reader below the derivation given one of
     * those would hold every declaration with nothing left saying it came out.
     */
    public Declarations<Derived.Def> declarations() {
        return table.declarations();
    }

    /** Every bare spelling that reaches a definition here, and the derived definition it reaches. */
    public Map<String, Derived.Def> reachable() {
        return table.reachable();
    }

    /**
     * What the derivation answered for {@code data}.
     *
     * <p>For a reader below the derivation that is holding the node — a checker walking a module, an
     * emitter writing a class — and needs what was derived for it. A product that got as far as
     * either came out, so the answer is here.
     *
     * <p>Refused rather than answered with nothing where it is not. A reader that met an absence
     * would have to decide what a product with no boundary representation means, and that is the
     * question this stage exists to have already answered; what it would be looking at is a module
     * the derivation did not answer for, handed to it by mistake.
     *
     * @throws IllegalStateException where nothing derived declares it
     */
    public Derived.Data derived(Hir.Data data) {
        if (table.declarations().declaration(data.declares()) instanceof Derived.Data answered) {
            return answered;
        }
        throw new IllegalStateException("`" + data.name()
                + "` is being read below the derivation, which did not answer for it");
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
