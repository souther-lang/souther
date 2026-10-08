package souther.compiler.meaning;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Rel;

import java.util.Comparator;
import java.util.List;
import java.util.Map;

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
     * A form of quantities against nought, facing the one way ({@link OneWay}).
     *
     * @param form        the comparison with its threshold moved in, so what it states is
     *                    {@code form proposition 0}
     * @param proposition the canonical relation
     */
    record Affine(LinearForm<Quantity> form, Rel proposition) implements Relation {

        public Affine {
            if (form == null || proposition != proposition.orItsDenial()) {
                throw new IllegalArgumentException("a relation is a form under the canonical one of"
                        + " a relation and its denial: " + form + " " + proposition);
            }
            if (OneWay.facesTheOtherWay(form)) {
                throw new IllegalArgumentException("a relation is written facing the one way, and "
                        + form + " faces the other");
            }
        }
    }

    /**
     * {@code form states 0}, written the one way every writing of it comes to: the form turned
     * until its first atom, in the order atoms spell themselves, has a positive coefficient, and the
     * relation the canonical one of it and its denial.
     *
     * <p><b>Which way is a fact about the relation and not about the source.</b> Read off the side
     * an author put first, {@code a >= b} and {@code b <= a} are two forms that are each other
     * negated, and two propositions where there is one statement. Turning a form turns its relation
     * as well — {@code f >= 0} is {@code -f > 0} not holding, and an equality is one either way — so
     * it is done here, once, for every reader that writes a relation down.
     *
     * @param form        what is compared with nought, facing the one way
     * @param proposition the canonical relation
     * @param holds       whether {@code form proposition 0} is what was stated, or its denial
     * @param <A>         the atoms the form is over
     */
    record OneWay<A extends Quantity>(LinearForm<A> form, Rel proposition, boolean holds) {

        /** {@code form states 0}, written one way. */
        public static <A extends Quantity> OneWay<A> of(LinearForm<A> form, Rel states) {
            Rel proposition = states.orItsDenial();
            boolean holds = states == proposition;
            if (!facesTheOtherWay(form)) {
                return new OneWay<>(form, proposition, holds);
            }
            return switch (proposition) {
                case GE -> new OneWay<>(form.negate(), Rel.GT, !holds);
                case GT -> new OneWay<>(form.negate(), Rel.GE, !holds);
                case EQ -> new OneWay<>(form.negate(), Rel.EQ, holds);
                case LE, LT, NE -> throw new IllegalStateException(
                        "a canonical relation is one of three, and " + proposition + " is not");
            };
        }

        /**
         * Whether the first coefficient, by the atoms' own order, is negative. Taken from the order
         * and not from every coefficient's sign, so a form with one of each sign faces one way too.
         */
        static <A extends Quantity> boolean facesTheOtherWay(LinearForm<A> form) {
            List<Map.Entry<A, ExactRatio>> walked = form.coefs().entrySet().stream()
                    .sorted(Comparator.comparing(each -> each.getKey().spelled())).toList();
            for (int at = 1; at < walked.size(); at++) {
                A before = walked.get(at - 1).getKey();
                A here = walked.get(at).getKey();
                if (before.spelled().equals(here.spelled()) && !before.equals(here)) {
                    throw new IllegalStateException("two atoms of one form are spelled alike: "
                            + before + " and " + here + "; which of them comes first would be left"
                            + " to how the comparison was written");
                }
            }
            return !walked.isEmpty() && walked.getFirst().getValue().signum() < 0;
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
