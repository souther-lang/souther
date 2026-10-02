package souther.compiler.check;

import souther.compiler.types.TypeSymbol;

import java.util.List;

/**
 * What a value of a sum can be: the leaf cases it reaches, and whether every one of them is a unit.
 *
 * <p>Not the declarations a sum lists. A case that is itself a sum is transparent as a value —
 * anything of the inner one is of the outer one (spec §sum-discrimination) — so what is answered is
 * what descending the list reaches, each leaf once, in the order the declarations write them and at
 * the place it was first reached. A reader wanting the one layer a sum writes is asking something
 * else, and {@link TypeOps#caseNames} is where that is read.
 *
 * <p>A fact about the sum's declaration and the sums under it, the same whoever asks. Ordering a
 * value of an enumeration, counting the places a case takes, writing how the set crosses a
 * boundary, listing which enumerations a unit is a case of — each of those reads the same leaves,
 * and a reader working them out for itself reads what every case of the sum is, every time. So the
 * answer is the compilation's to hold, once for each sum, and the descent is reached through
 * {@link #asWritten} and nothing else: what a type is made of is composed out of what this answers.
 *
 * <p>Whether the sum is an enumeration is answered with the leaves and not beside them. It is what
 * the leaves say about themselves, read in the same walk, and an answer that held the leaves
 * without it would send every reader asking it back to what each leaf is.
 */
@FunctionalInterface
public interface SumCases {

    /**
     * What a value of {@code sum} can be, or null where {@code sum} is not a sum.
     *
     * <p>Null and not an answer with no leaves: a sum whose cases reach nothing is a sum, and a
     * declaration of another form has no cases to have reached. Every reader asks this of a name
     * it already knows the form of.
     */
    Cases of(TypeSymbol.AtModule sum);

    /** Nothing declared anywhere — for a reading over primitives, which asks of no declaration. */
    SumCases NONE = _ -> null;

    /**
     * The same question read off the declarations, each time it is asked: the descent itself.
     *
     * <p>For the compilation's answer, which is made by asking it once for each sum, and for the
     * walks that have not been handed that answer.
     */
    static SumCases asWritten(DeclarationKinds kinds, PublishedDeclarations published) {
        return sum -> kinds.isSum(sum.key())
                ? Cases.of(AtomSpace.leavesUnder(List.of(sum), kinds, published), kinds)
                : null;
    }

    /**
     * The leaves of one sum, and which of the two it is.
     *
     * <p>Sealed over exactly that: every leaf a unit, or not. A sum with no leaf at all is not an
     * enumeration — it has no values to order and none to write as a bare tag — so it is the
     * second.
     */
    sealed interface Cases {

        /** The leaf cases, in the order the descent reached them. Never empty for an
         *  {@link Enumeration}. */
        List<TypeSymbol> cases();

        /** {@code cases} as the arm the leaves say they are. */
        static Cases of(List<TypeSymbol> cases, DeclarationKinds kinds) {
            return everyOneAUnit(cases, kinds)
                    ? new Enumeration(cases)
                    : new NonEnumeration(cases);
        }

        private static boolean everyOneAUnit(List<TypeSymbol> cases, DeclarationKinds kinds) {
            if (cases.isEmpty()) {
                return false;
            }
            for (TypeSymbol leaf : cases) {
                if (!(leaf instanceof TypeSymbol.AtModule at
                        && kinds.of(at.key()) == DeclarationKind.UNIT)) {
                    return false;
                }
            }
            return true;
        }
    }

    /**
     * A sum every leaf of which is a unit: an enumeration, carrying nothing but which case it is,
     * and ordered by the order its leaves are declared in (ADR-0069).
     */
    record Enumeration(List<TypeSymbol> cases) implements Cases {

        public Enumeration {
            cases = List.copyOf(cases);
            if (cases.isEmpty()) {
                throw new IllegalArgumentException(
                        "an enumeration has a case to be, or it has no values to order");
            }
        }
    }

    /** A sum at least one leaf of which carries something, or that reaches no leaf at all. */
    record NonEnumeration(List<TypeSymbol> cases) implements Cases {

        public NonEnumeration {
            cases = List.copyOf(cases);
        }
    }
}
