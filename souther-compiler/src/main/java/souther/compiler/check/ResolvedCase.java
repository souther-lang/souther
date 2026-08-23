package souther.compiler.check;

import souther.compiler.types.CaseSelector;
import souther.compiler.types.Refinement;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.List;

/**
 * A case as this compile resolved it: what selects it, and which atoms selecting it covers.
 *
 * <p>Two facts of different phases, held together because one reader needs both and neither can be
 * worked out from the other. A {@link CaseSelector} is what a value is tested as and read as at run
 * time, and it says that much about itself wherever it is written — {@code Some} carries the present
 * carrier, a data-named case carries its data type — with no program around it. What it
 * <em>covers</em> is not like that: a case that is itself a sum stands for the leaves under it
 * (spec §sum-data), and which leaves those are is a fact about the declarations this compile read.
 *
 * <p>So the atoms are not a component of the selector. Putting them there would make a selector
 * whose name and carrier agree and whose atoms do not — the half-decided state
 * {@code CaseSelector}'s own constructor exists to refuse, and one it could not refuse, since
 * nothing in {@code types} can ask what a name reaches. The phase boundary is the type instead:
 * below it a case is a selector, and at this level it is a selector that has been resolved against
 * the declarations.
 *
 * <p>Made in this package and read anywhere. There is no way to say what a case covers: the
 * constructor is private and every way in takes the causes only — a name and the symbols to resolve
 * it against, or the element an optional holds — so the atoms are worked out and never supplied. A
 * constructor taking them would have moved the half-decided state rather than removed it, since a
 * caller here could hand {@code Station}'s selector the leaves of {@code Hospital} and nothing
 * could tell. The factories are package-private on top of that, so the backend reads one and mints
 * none; but a tripwire over the mint sites is the lesser guard, and the value is already
 * unrepresentable without it.
 *
 * <p>What is emitted downstream is the selector — {@link #selector()} — which is all {@code Core}
 * and the backend have ever needed.
 */
public final class ResolvedCase {

    private final CaseSelector selector;
    private final List<TypeSymbol> atoms;

    private ResolvedCase(CaseSelector selector, List<TypeSymbol> atoms) {
        this.selector = selector;
        this.atoms = List.copyOf(atoms);
    }

    /**
     * A case whose carrier is the value: a union member, or a case of a named sum.
     *
     * <p>Resolved against {@code symbols} here rather than handed the answer. What it covers is read
     * from what it holds and not from its name: the {@code Int} of {@code Int | DivisionByZero}
     * holds a primitive, which {@link CaseSelector#heldBy} has already worked out, and a case that
     * is a sum holds that sum and covers the leaves under it.
     *
     * <p>A name that denotes no type holds nothing to descend — {@code Raw}, which a stage may be
     * unioned with and which no declaration takes apart — and covers no atom. The same answer
     * {@link AtomSpace} gives a type that names no case, said here because the type to ask it about
     * is the one that is missing.
     */
    static ResolvedCase direct(TypeSymbol name, Symbols symbols) {
        CaseSelector selector = CaseSelector.direct(name);
        Type held = selector.bound();
        return new ResolvedCase(selector,
                held == null ? List.of() : AtomSpace.subjectAtoms(held, symbols));
    }

    /**
     * The carrier an optional holding {@code element} is.
     *
     * <p>No symbols, because there is nothing to resolve: what {@code Some} covers is {@code Some}.
     * Taking the element's atoms would make an optional over a sum cover that sum's leaves, and the
     * two arms of a {@code match} over it would be held against cases no optional has.
     */
    static ResolvedCase optionPresent(Type element) {
        return new ResolvedCase(CaseSelector.optionPresent(element), List.of(TypeSymbol.SOME));
    }

    /** The carrier an optional holding nothing is, which covers itself as the present one does. */
    static ResolvedCase optionAbsent() {
        return new ResolvedCase(CaseSelector.optionAbsent(), List.of(TypeSymbol.NONE));
    }

    /** What tests and reads the value — what {@code Core} carries and the backend emits. */
    public CaseSelector selector() {
        return selector;
    }

    /**
     * The atoms a value selected by this can be, in first-reach declaration order.
     *
     * <p>Worked out by whichever factory made this and never supplied to one. See {@link #direct}
     * for a case whose carrier is the value and {@link #optionPresent} for an optional's.
     */
    public List<TypeSymbol> atoms() {
        return atoms;
    }

    /** The name this case is written by. */
    public TypeSymbol name() {
        return selector.name();
    }

    /** What the value turns out to be once this case is selected. */
    public Refinement refinement() {
        return selector.refinement();
    }

    /** What a value selected by this is read as, or null where nothing readable stands under it. */
    public Type bound() {
        return selector.bound();
    }

    /**
     * Two resolved cases are one where they select the same case and cover the same atoms.
     *
     * <p>A value and not an identity. It is kept in what a behavior's declaration comes to, and two
     * compiles of one source have to answer alike — a reader comparing what was stated before an
     * edit with what is stated after would otherwise see every rule change because the objects are
     * new ({@code EquivalentDatabasesAnswerTheSameTest}).
     *
     * <p>The atoms are compared as well as the selector. They follow from the selector and the
     * declarations, so within one compile the two never disagree; comparing both says that plainly
     * rather than resting on it, and two compiles of different sources that resolved one selector
     * differently are two different things.
     */
    @Override
    public boolean equals(Object other) {
        return other instanceof ResolvedCase that
                && selector.equals(that.selector) && atoms.equals(that.atoms);
    }

    @Override
    public int hashCode() {
        return 31 * selector.hashCode() + atoms.hashCode();
    }

    @Override
    public String toString() {
        return selector.name() + " covering " + atoms;
    }
}
