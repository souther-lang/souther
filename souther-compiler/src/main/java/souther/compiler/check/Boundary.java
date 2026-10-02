package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.types.CaseShape;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.List;

/**
 * How the alternatives a value can be are written at a boundary: which form the set travels as, what
 * tag each alternative wears, and — where the form has them — the key that tag stands under and the
 * key a {@link CaseShape#WRAPPED} case's standalone representation stands under beside it.
 *
 * <p>A named sum and a behavior's output union are one question asked of two spellings. Both are a
 * set of alternatives that has to cross, and both are answered here through the same call, so
 * neither can be given a form, a tag or a key the other was not. They used to be answered in five
 * places that read none of the others, and two of them disagreeing went unreported because every one
 * of them dispatches on the first alternative that answers (#990, #994).
 *
 * <p>Nothing of this is stored. The representation is derived (ADR-0004) and a declaration says
 * nothing about it, so a field on {@link Hir.SumData} holding it would be an answer that can drift
 * from the one a reader works out — and a union, which has no declaration to hold a field, could not
 * be given one at all. That is what made the union a separate path in the first place.
 *
 * <p>The boundary here is where a value crosses into or out of the program, which is what
 * {@link BoundaryInput} and {@link BoundaryOutput} are about. It is not the boundary of
 * {@code query.BoundaryDerivation} and {@code partition.BoundaryPolicy}, which is the line a rule
 * draws between two classes of input. The two never meet: this answers how a value is written, and
 * that one answers where a rule divides. Said because the word carries both in this compiler and a
 * reader arriving at one from the other has to be told which.
 *
 * <p>What is <em>not</em> here: which atoms there are, which is {@link AtomSpace}'s and is read from
 * it; what a case carries and therefore whether the tag can sit beside it, which is
 * {@link TypeOps#caseShape}'s; whether every leaf of a named sum is a unit, which is a fact about
 * its declarations that {@link SumCases} holds; and what the language makes of that fact, which is
 * {@link TypeOps#isUnitOnlySum}'s and is read by what counts a type's values and by what orders
 * them. The fact is one and is read here as it is held. What follows from it is two policies, the
 * language's and this one, and each stays its own: folding the language's into here would make one
 * answer decide how a value is ordered and how it is written.
 */
public final class Boundary {

    private Boundary() {}

    /** The key a derived codec writes an alternative's tag under (spec §encoder-derivation). */
    private static final String DISCRIMINATOR = "type";

    /** The key a derived codec writes a {@link CaseShape#WRAPPED} case's standalone representation
     *  under, beside the tag (spec §sum-discrimination). */
    private static final String CONTENTS = "value";

    /**
     * How {@code subject}'s alternatives are written at a boundary.
     *
     * <p>Answers for anything, not only for a sum or a union — {@link AtomSpace#subjectAtoms} does,
     * and a caller that has to know the shape before it may ask would be deciding here what a
     * boundary form is. What comes back for a type that is no alternative space at all is
     * {@link Representation.Discriminated}, which is the right answer to the one question such a
     * caller asks — a product, a newtype, a primitive and a standalone unit are none of them read as
     * a bare tag — and is not a claim that the type crosses as a discriminated object. A reader
     * wanting the whole external representation of an arbitrary type is not asking this.
     */
    public static Alternatives of(Type subject, DeclarationKinds kinds, SumCases sums) {
        List<TypeSymbol> atoms = AtomSpace.subjectAtoms(subject, kinds, sums);
        return new Alternatives(atoms, isEnumerationForm(subject, atoms, kinds, sums)
                ? new Representation.Enumeration()
                : new Representation.Discriminated(DISCRIMINATOR, CONTENTS));
    }

    /**
     * Whether the set travels as a bare tag: it is an alternative space, and every alternative in it
     * carries nothing but which one it is (spec §sum-discrimination).
     *
     * <p>Being an alternative space is a term of this and not a guard on {@link #of}. A standalone
     * unit is one atom and that atom is a unit, so the atoms alone would call it an enumeration —
     * and a unit crosses on its own as an empty object, the bare name being the form of an
     * enumeration and not of its unit cases (spec §encoder-derivation). The atoms answer what the
     * alternatives are; they do not answer whether there is a set of them.
     *
     * <p>Whether every alternative of a named sum is a unit is a fact about the sum's declarations,
     * and {@code sums} already holds it; what is this form's is only that such a set travels as a
     * bare tag. A name that is no sum has no answer there, which is the standalone unit above. A
     * union is no declaration and holds no answer of its own, so its members are asked here.
     */
    private static boolean isEnumerationForm(Type subject, List<TypeSymbol> atoms,
                                             DeclarationKinds kinds, SumCases sums) {
        if (subject instanceof Type.Ref(TypeSymbol.AtModule named)) {
            return sums.of(named) instanceof SumCases.Enumeration;
        }
        return subject instanceof Type.Union
                && !atoms.isEmpty()
                && atoms.stream().allMatch(atom -> atom instanceof TypeSymbol.AtModule at
                        && kinds.of(at.key()) == DeclarationKind.UNIT);
    }

    /**
     * One alternative space, settled: what it is made of and how that is written.
     *
     * <p>Handed to what generates and what checks, rather than each of them being handed the type
     * and asking again. Both would answer alike — this is a function of the type — but a reader
     * holding the type and the symbols is a reader that can work the tag out itself, and five of
     * them did.
     */
    public record Alternatives(List<TypeSymbol> atoms, Representation representation) {

        public Alternatives {
            atoms = List.copyOf(atoms);
        }

        /**
         * The alternatives as they are written, in the order {@link AtomSpace} put them in.
         *
         * <p>Derived and not held beside {@link #atoms}. A second list of the same set is what #990
         * was: the two are written from one walk, agree on the day they are written, and the day one
         * of them is extended nothing says which is the set.
         */
        public List<WireCase> wireCases() {
            return atoms.stream().map(atom -> new WireCase(atom, atom.name())).toList();
        }
    }

    /**
     * One alternative as it crosses: which atom it is, and the tag it wears.
     *
     * <p>The tag is an atom's name. That it is unique is not a rule invented here — ADR-0081 has
     * every effective member of a union going by a name of its own, and a sum's cases are declared
     * with it — so the map from atom to tag is injective on arrival.
     */
    public record WireCase(TypeSymbol atom, String tag) {}

    /** The form the set of alternatives travels as. */
    public sealed interface Representation {

        /** Every alternative carries nothing but which one it is, so the value is the tag itself. */
        record Enumeration() implements Representation {}

        /**
         * An alternative carries something of its own, so each alternative's tag stands under
         * {@code tagKey} (spec §sum-discrimination).
         *
         * <p>A {@link CaseShape#PRODUCT} or {@link CaseShape#UNIT} case carries the tag in the object
         * membership gives it. A {@link CaseShape#WRAPPED} case keeps its standalone representation
         * unchanged and places it under {@code contentsKey} beside the tag. Which shape a case has is
         * {@link TypeOps#caseShape}'s answer, read from the declaration; the two keys are this form's,
         * and a reader writing it spells neither.
         *
         * <p>The two keys differ. A wrapped case writes both into one object, and one key would leave
         * the representation standing where the tag was, which no decoder reads back.
         */
        record Discriminated(String tagKey, String contentsKey) implements Representation {

            public Discriminated {
                if (tagKey.equals(contentsKey)) {
                    throw new IllegalArgumentException(
                            "the tag and a wrapped case's representation cannot stand under one key: "
                                    + tagKey);
                }
            }
        }
    }
}
