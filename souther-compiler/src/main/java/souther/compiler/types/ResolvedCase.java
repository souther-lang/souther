package souther.compiler.types;

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
 * <p>There is no way to say what a case covers: the constructor is private and the one way in —
 * {@link #resolve} — takes the causes only, a selector and a way of descending the type it stands
 * over, so the atoms are worked out and never supplied. A constructor taking them would have moved
 * the half-decided state rather than removed it, since a caller could hand {@code Station}'s
 * selector the leaves of {@code Hospital} and nothing could tell.
 *
 * <p>The value is here and the resolving is not. What a case covers is read off the declarations,
 * which this package holds none of; {@link Atoms} is that reading asked for rather than done, and
 * the module that read them answers it. So a resolved case carries no compiler in it and is read by
 * an output that names none.
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
     * {@code selector} resolved against the declarations {@code symbols} holds.
     *
     * <p>The one way in, and it takes the causes only: a selector, which is self-validating and says
     * what it tests and reads, and a reading of what a type reaches to work out what it covers.
     * There is no way to state the atoms, so a case covering leaves it does not reach is not a value
     * that can be written.
     *
     * <p>Also where a selector that came back from {@code Core} is made whole again. A pass reading
     * an elaborated arm has the selector and not what it covers — {@code Core} carries nothing about
     * the program around it — and asking here is that pass crossing back into this one, not a second
     * reading: what a case covers is worked out in this method and nowhere else.
     */
    public static ResolvedCase resolve(CaseSelector selector, Atoms atoms) {
        return new ResolvedCase(selector, covers(selector, atoms));
    }

    /**
     * What selecting {@code selector} covers.
     *
     * <p>Read from the refinement and not from the name, because the two carriers that are not a
     * case of a declaration are told apart by nothing else. An optional's carrier covers itself:
     * what {@code Some} covers is {@code Some}, and taking the element's atoms would make an
     * optional over a sum cover that sum's leaves, so the two arms of a {@code match} over it would
     * be held against cases no optional has.
     *
     * <p>A case whose carrier is the value covers what it holds — one atom for a leaf, and the
     * leaves under it for a case that is itself a sum. A name that denotes no type holds nothing to
     * descend ({@code Raw}, which a stage may be unioned with and which no declaration takes apart)
     * and covers no atom: the answer {@link Atoms} gives a type that names no case, said here
     * because the type to ask it about is the one that is missing.
     */
    private static List<TypeSymbol> covers(CaseSelector selector, Atoms atoms) {
        return switch (selector.refinement()) {
            case Refinement.OptionPresent _ -> List.of(TypeSymbol.SOME);
            case Refinement.OptionAbsent _ -> List.of(TypeSymbol.NONE);
            case Refinement.Direct direct -> direct.bound() == null
                    ? List.of()
                    : atoms.of(direct.bound());
        };
    }

    /** What tests and reads the value — what {@code Core} carries and the backend emits. */
    public CaseSelector selector() {
        return selector;
    }

    /**
     * The atoms a value selected by this can be, in first-reach declaration order.
     *
     * <p>Worked out by {@link #resolve} and never supplied to it.
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
