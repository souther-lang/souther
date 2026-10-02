package souther.compiler.check;

import souther.compiler.types.CanonicalNameOrder;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * The atoms a type is made of: the cases a value of it can be that are not themselves sums.
 *
 * <p>A sum whose case is a sum is transparent as a value — anything of the inner one is of the
 * outer one (spec §sum-data) — so what a value of the outer sum can be is not its case list but
 * what descending that list reaches. That descent is what this is, and it is written once. Four
 * readers used to write it themselves, each keyed on what suited it, and they answered differently
 * where the descent reaches one case twice.
 *
 * <p>An atom here is a <em>case</em> identity and not the atom of {@link Terms} and the numeric
 * readings, which is a term a reading cannot take further apart. The two never meet: this answers
 * what a value may be, and that one names where a value came from. Said because the word carries
 * both in this compiler and a reader arriving at one from the other has to be told which.
 *
 * <p>An atom is one per {@link TypeSymbol}. Two cases naming one type are one atom however many
 * declarations reach it: the type is what a value is, what a codec tags, and what an arm tests, so
 * a reader keyed on anything else counts one thing as two.
 *
 * <p>What comes out is unique and deterministic. Within a declaration it is the order the cases are
 * written in, first reach keeping the place — a derived codec writes its variants in it (spec
 * §sum-discrimination), so an order that came out of whichever collection was reached for would
 * move a generated artifact nothing about the program had changed. An anonymous union holds its
 * members as a set and states no order of its own, so its members are taken in their name's order
 * rather than in the set's: an order nothing decided is one that can differ between two runs of one
 * compiler, which is the same defect from further away.
 */
public final class AtomSpace {

    private AtomSpace() {}

    /**
     * What a value of {@code t} can be, descending every case that is itself a sum.
     *
     * <p>Answers for anything, not only a sum: a type that is no sum is the one atom it is, and a
     * type that names no case at all — an optional, a type the compiler could not work
     * out — has none. Which of those a reader treats as an answer and which as a refusal is the
     * reader's, and asking here does not decide it.
     *
     * <p>One entry and not one per shape. A sum asked about through its declaration rather than its
     * type would be a second way of deciding where the descent starts, and the two would answer
     * alike until the day one of them was extended.
     *
     * <p>Composed and not descended. What a sum the type names reaches is {@code sums}' answer for
     * that sum, and what is done here is to put the answers for the names the type states side by
     * side, each leaf once at the place it was first reached. That is the leaves one descent from
     * all of the names would reach: a sum met from a second name was taken apart under the first,
     * so everything under it is already in place.
     *
     * <p>Whether a name is a sum is asked of {@code kinds}, and only a sum is asked of {@code
     * sums}. Which form a declaration is, is the one thing known of it before what it says.
     */
    public static List<TypeSymbol> subjectAtoms(Type t, DeclarationKinds kinds, SumCases sums) {
        List<TypeSymbol> roots = roots(t);
        // One sum is its own answer, handed on as it is: laid beside nothing, it has nothing to
        // be put in order with, and copying it would pay for every leaf on each question.
        if (roots.size() == 1 && reached(roots.getFirst(), kinds, sums) instanceof SumCases.Cases one) {
            return one.cases();
        }
        Set<TypeSymbol> atoms = new LinkedHashSet<>();
        for (TypeSymbol root : roots) {
            SumCases.Cases reached = reached(root, kinds, sums);
            if (reached == null) {
                atoms.add(root);
            } else {
                atoms.addAll(reached.cases());
            }
        }
        return List.copyOf(atoms);
    }

    /**
     * What {@code sums} answers for the one sum {@code t} names, or null where it names none.
     *
     * <p>For a reader that wants both what a value of the sum can be and which of the two it is:
     * one answer holds both, so it is taken here once and read for each. Going back through
     * {@link #subjectAtoms} for the leaves would ask the same sum again.
     */
    public static SumCases.Cases sumNamedBy(Type t, DeclarationKinds kinds, SumCases sums) {
        return t instanceof Type.Ref ref ? reached(ref.name(), kinds, sums) : null;
    }

    /** What {@code sums} answers for {@code name}, or null where it is no sum. */
    private static SumCases.Cases reached(TypeSymbol name, DeclarationKinds kinds, SumCases sums) {
        return name instanceof TypeSymbol.AtModule at && kinds.isSum(at.key()) ? sums.of(at) : null;
    }

    /**
     * The leaves under {@code roots}, descending every one of them that is a sum: the descent
     * itself, which {@link SumCases#asWritten} asks of one sum at a time.
     *
     * <p>One descent over all of them, so a sum reached from two roots is taken apart once and its
     * leaves stand where the first root reached them. Package-private so that what
     * {@link #subjectAtoms} composes out of one answer per root can be held to it.
     *
     * <p>Asked of what the declarations publish and not of a world's declarations. Which cases a sum
     * has is what that declaration says about itself, so a reader here means nothing by the tree it
     * was written in — and reading one would answer differently for the same sum every time a line
     * above it moved.
     *
     * <p>Whether a name is a sum to descend is asked of {@code kinds} first, and what it says only
     * of the ones that are. A case may be a product, whose meaning is made by reading its clauses,
     * and a clause that orders a value asks this of the sums of the value's module. Asking every
     * case what it says would ask it of a product whose own meaning is being made.
     */
    static List<TypeSymbol> leavesUnder(List<TypeSymbol> roots, DeclarationKinds kinds,
                                        PublishedDeclarations published) {
        Set<TypeSymbol> atoms = new LinkedHashSet<>();
        descend(roots, kinds, published, atoms, new HashSet<>());
        return List.copyOf(atoms);
    }

    /**
     * The names to descend from, in the order the type states them.
     *
     * <p>A union holds its members in one order whoever built it, so there is nothing to put on it
     * here. Everything else names one type and there is nothing to order.
     */
    private static List<TypeSymbol> roots(Type t) {
        if (t instanceof Type.Union union) {
            return statedBy(union);
        }
        return List.copyOf(TypeOps.namesOf(t));
    }

    /**
     * The members of {@code union}, in the order it states them.
     *
     * <p>Read and not decided. A union is built with its members in the order they are shown
     * ({@link CanonicalNameOrder}), so arranging them again here would be a second owner of one
     * order — and the one that went untested would be whichever of the two somebody later changed.
     */
    static List<TypeSymbol> statedBy(Type.Union union) {
        return List.copyOf(union.members());
    }

    /**
     * Collects the atoms under {@code names}, descending the ones that are sums.
     *
     * <p>{@code expanded} is the sums already taken apart, which is what a sum reaching itself
     * terminates on and what keeps a sum reached through two cases from being descended twice.
     * Such a declaration is refused where it is written ({@link DataChecker}); this only has to
     * come back.
     */
    private static void descend(Iterable<TypeSymbol> names, DeclarationKinds kinds,
                                PublishedDeclarations published, Set<TypeSymbol> atoms,
                                Set<TypeSymbol> expanded) {
        for (TypeSymbol name : names) {
            // What the language declares is a case and never a sum, and it has no address to ask
            // about: a name that is not a module's is an atom without anything being asked.
            if (name instanceof TypeSymbol.AtModule at
                    && kinds.isSum(at.key())
                    && published.of(at.key())
                        instanceof PublishedDeclarationResult.Found(DeclarationMeaning.Sum sum)) {
                if (expanded.add(name)) {
                    descend(declaredCases(sum), kinds, published, atoms, expanded);
                }
            } else {
                atoms.add(name);
            }
        }
    }

    /** The declarations {@code sum} lists, in the order it lists them. A name it lists that reaches
     *  nothing is no case: it is reported where it is written, and a reader counting what a value
     *  can be counts what is there. */
    static List<TypeSymbol> declaredCases(DeclarationMeaning.Sum sum) {
        List<TypeSymbol> named = new ArrayList<>();
        for (DeclarationReference each : sum.cases()) {
            if (each instanceof DeclarationReference.Named it) {
                named.add(it.declaration());
            }
        }
        return named;
    }
}
