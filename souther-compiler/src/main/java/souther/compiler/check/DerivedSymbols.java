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
 * <p>Three tables and each answers what it settled. A declaration is read as it was normalized,
 * a representation is asked of what the derivation answered for, and whether a name is declared at
 * all is resolution's. Written as one table with the others read where it came up empty, the
 * derivation's failure on one declaration would choose the form every reader saw that declaration
 * in, which is a question none of them asked.
 *
 * <p>Each table's second source is at the rung that table reads: the language's own vocabulary is
 * lifted to the derived representation ({@link Declarations.Vocabulary#ofDerived}) and to the
 * normalized one ({@link Declarations.Vocabulary#ofNormalized}), so a reader here is never handed a
 * library declaration through a node the two could both be read as.
 */
public final class DerivedSymbols implements Symbols {

    /**
     * The declarations a representation was derived for.
     *
     * <p>Read by the questions a representation answers and by no others. A declaration missing here
     * is a product one of whose fields names no type, and what that costs is that nobody can be told
     * how a value of it crosses.
     */
    private final SymbolTable<Derived.Def> table;
    /**
     * The same names over the declarations as they were normalized.
     *
     * <p>What a declaration is read as here. Normalizing is answered for every declaration a module
     * writes, so this is not missing the ones the derivation could not answer for — which is the
     * whole point of its being a table of its own. Read from the derived table instead, a reader
     * would be handed the constructions written as constructions where a codec came out and the
     * calls the author typed where one did not, and nothing it held would say which.
     */
    private final SymbolTable<Normalized.Def> normalized;
    /**
     * The same names over the declarations as resolution left them.
     *
     * <p>Which names are declared, by which module, and what a spelling written here means. Asked of
     * resolution because that is what settled them: a declaration no representation could be derived
     * for is a name this module declares all the same, and a reader told otherwise would say the
     * name is the language's, or that the value has no field to read, or that this compilation has
     * no such type. What one achievement could not do does not decide what another established —
     * which is the same reason the two tables above are two.
     */
    private final SymbolTable<Hir.Def> resolved;

    private DerivedSymbols(SymbolTable<Derived.Def> table, SymbolTable<Normalized.Def> normalized,
                           SymbolTable<Hir.Def> resolved) {
        this.table = table;
        this.normalized = normalized;
        this.resolved = resolved;
    }

    /** A module over the three registries a reader below the derivation is answered from, each with
     * the language's own vocabulary at the rung that registry reads. */
    public static DerivedSymbols over(String module, Registry<Derived.Def> registry,
                                      Registry<Normalized.Def> normalized,
                                      Registry<Hir.Def> resolved, Denoting names, Stdlib stdlib) {
        return new DerivedSymbols(
                new SymbolTable<>(module, registry, names,
                        Declarations.Vocabulary.ofDerived(stdlib), stdlib,
                        each -> each.declaration().node()),
                new SymbolTable<>(module, normalized, names,
                        Declarations.Vocabulary.ofNormalized(stdlib), stdlib, Normalized.Def::node),
                new SymbolTable<>(module, resolved, names,
                        Declarations.Vocabulary.of(stdlib), stdlib, each -> each));
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

    /** Every bare spelling in scope here, and the derived declaration it reaches — which is not
     *  every spelling, because a declaration nothing derived a representation for has none. */
    public Map<String, Derived.Def> reachable() {
        return table.reachable(resolved.scope());
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

    /**
     * What a name written here means.
     *
     * <p>Resolution's, like the questions above it. A scope answers which declaration a spelling
     * denotes, and it works that out by asking its registry whether a declaration is there — so a
     * scope over the derived table would answer that a name nothing derived a representation for
     * denotes nothing, and a reader spelling it out in full would be told this compilation has no
     * such type. That is the same mistake as reading a declaration from the derived table, one
     * lookup over.
     */
    @Override
    public TypeScope scope() {
        return resolved.scope();
    }

    /**
     * The declaration {@code name} is, normalized.
     *
     * <p>One table and one form. Every declaration a module writes is normalized, so which form this
     * answers with is not decided by whether a representation could be derived for the declaration
     * asked about — a reader here holds the constructions written as constructions, of every
     * declaration, or the name is one nothing declares.
     */
    @Override
    public Hir.Def declaredNode(TypeSymbol name) {
        return normalized.declaredNode(name);
    }

    /** The same, of an address. */
    @Override
    public Hir.Def declaredNode(TypeKey address) {
        return normalized.declaredNode(address);
    }

    @Override
    public boolean declares(TypeKey address) {
        return resolved.declares(address);
    }

    @Override
    public boolean declaredByCompilation(TypeSymbol name) {
        return resolved.declaredByCompilation(name);
    }

    @Override
    public boolean declaredByCompilation(TypeKey address) {
        return resolved.declaredByCompilation(address);
    }

    @Override
    public Set<String> declaredNamesIn(String module) {
        return resolved.declaredNamesIn(module);
    }

    // What is left is neither a declaration nor a name of one: the module this is a scope of, and
    // the library it was compiled against. The three tables hold the same answer to each, being
    // built over one module and one library — and they are asked of the resolution all the same, so
    // that the partial table is read by the three questions above it and by nothing else. A reader
    // of this file can see which questions those are without working out whether the answer happens
    // to be the same.

    @Override
    public String module() {
        return resolved.module();
    }

    @Override
    public Stdlib library() {
        return resolved.library();
    }

    @Override
    public ValueName.Stdlib.Operation theWalk() {
        return resolved.theWalk();
    }

    @Override
    public ValueName.Stdlib.Operation theDistinctnessPredicate() {
        return resolved.theDistinctnessPredicate();
    }

    @Override
    public Kernel kernelOf(ValueName.Stdlib.Operation operation) {
        return resolved.kernelOf(operation);
    }
}
