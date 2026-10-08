package souther.compiler.meaning;

import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Rel;

/**
 * A comparison as the relation it states over the quantities a condition is about, in the one
 * spelling every writing of it comes to.
 *
 * <p>The proposition is the canonical one of a relation and its denial
 * ({@link Rel#orItsDenial}), so {@code n > 100} and {@code n <= 100} are one relation, held one way
 * and the other — which way is the proposition's to say ({@link Proposition.Compared}), not this.
 */
public sealed interface Relation {

    /** The relation this states, which is the canonical one of the pair. */
    Rel proposition();

    /**
     * A form of quantities against nought.
     *
     * @param form        the comparison with its threshold moved in, so what it states is
     *                    {@code form proposition 0}
     * @param proposition the canonical relation
     */
    record Affine(LinearForm<DecisionAtom> form, Rel proposition) implements Relation {

        public Affine {
            if (form == null || proposition != proposition.orItsDenial()) {
                throw new IllegalArgumentException("a relation is a form under the canonical one of"
                        + " a relation and its denial: " + form + " " + proposition);
            }
        }
    }

    /**
     * One quantity against a written place on the order it stands on, where there is no sum to
     * move the place into: two strings do not add.
     */
    record Ordered(DecisionAtom term, Place at, Rel proposition) implements Relation {

        public Ordered {
            if (term == null || at == null || proposition != proposition.orItsDenial()) {
                throw new IllegalArgumentException("a relation on an order is a quantity, a place"
                        + " and the canonical one of a relation and its denial");
            }
        }
    }
}
