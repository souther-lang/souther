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
 * <p>Made in this package and read anywhere. The constructor is package-private because the atoms
 * have one correct value and {@link CaseSpace} is where it is worked out; a caller elsewhere could
 * only restate it, and a restatement that drifted would be a case covering leaves it does not.
 * What is emitted downstream is the selector — {@link #selector()} — which is all
 * {@code Core} and the backend have ever needed.
 */
public final class ResolvedCase {

    private final CaseSelector selector;
    private final List<TypeSymbol> atoms;

    ResolvedCase(CaseSelector selector, List<TypeSymbol> atoms) {
        if (selector == null || atoms == null) {
            throw new IllegalArgumentException("a resolved case is a selector and what it covers");
        }
        this.selector = selector;
        this.atoms = List.copyOf(atoms);
    }

    /** What tests and reads the value — what {@code Core} carries and the backend emits. */
    public CaseSelector selector() {
        return selector;
    }

    /**
     * The atoms a value selected by this can be, in first-reach declaration order.
     *
     * <p>{@link AtomSpace#subjectAtoms} of what the case holds, which is one atom for a leaf and the
     * leaves under it for a case that is a sum. An optional's carriers are not asked that way: what
     * {@code Some} covers is {@code Some} and not the atoms of the element it holds, so its own name
     * is the atom. Reading them through the element would make an optional over a sum cover that
     * sum's leaves, and the arms of a {@code match} over an optional would be held against cases no
     * optional has.
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
