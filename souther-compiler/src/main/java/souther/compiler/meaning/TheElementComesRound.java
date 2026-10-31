package souther.compiler.meaning;

import souther.compiler.numeric.ExactRatio;

import java.math.BigInteger;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;

/**
 * That a statement over the element of a list of every whole number between two comes out on an
 * element as it does on the element {@code every} past it.
 *
 * <p>Said of a statement that is relations of numbers held together, all of them or any one, each
 * relation a form of the input's numbers and of remainders. The element is weighed only inside the
 * dividends of those remainders, and by a whole number, so each remainder leaves the same on two
 * elements its divisor apart, and every relation, and so the whole statement, comes out the same on
 * two elements as many apart as every divisor goes into. A relation weighing the element anywhere
 * else, or any other kind of statement, is no such statement: what it says of the element need not
 * come round at all.
 *
 * <p>What the statement comes to on an element, not what a run makes of it: whether a run reaches
 * the element, and what working it out does to the run on the way, is asked of the run.
 *
 * @param element the element, the one value read off a binding the statement weighs
 * @param number  which whole numbers the list holds
 * @param every   how many elements apart the statement comes out the same
 */
public record TheElementComesRound(Quantity.OfABinding element, Quantity.AWholeNumberInTurn number,
                                   BigInteger every) {

    public TheElementComesRound {
        Objects.requireNonNull(element, "the statement comes round over some element");
        Objects.requireNonNull(number, "of a list of some whole numbers");
        if (every.signum() <= 0) {
            throw new IllegalArgumentException("a statement comes round in some elements: " + every);
        }
    }

    /** That {@code stated} comes round over the element of such a list — or nothing where it is no
     *  statement of that kind. */
    public static Optional<TheElementComesRound> in(Proposition stated) {
        Walk walk = new Walk();
        if (!walk.through(stated) || walk.element == null
                || !(walk.element.handed().orElse(null) instanceof Quantity.AWholeNumberInTurn
                        number)) {
            return Optional.empty();
        }
        return Optional.of(new TheElementComesRound(walk.element, number, walk.every));
    }

    /** The element found so far, and how many elements the remainders weighing it come round in. */
    private static final class Walk {

        private Quantity.OfABinding element;
        private BigInteger every = BigInteger.ONE;

        /** Whether {@code stated} is of that kind, as far as what has been walked says. */
        boolean through(Proposition stated) {
            return switch (stated) {
                case Proposition.Always _ -> true;
                case Proposition.All(var parts, var _) -> parts.stream().allMatch(this::through);
                case Proposition.Any(var parts, var _) -> parts.stream().allMatch(this::through);
                case Proposition.Compared(Relation.Affine affine, boolean _, var _) ->
                        affine.form().coefs().keySet().stream().allMatch(this::weighs);
                default -> false;
            };
        }

        /** Whether {@code each}, a quantity a relation weighs, is a number of the input or a
         *  remainder weighing the element only as a whole number of it. */
        private boolean weighs(Quantity each) {
            if (each instanceof DecisionAtom.OfTheInput) {
                return true;
            }
            if (!(each instanceof Quantity.RemainderOfADividend remainder)) {
                return false;
            }
            boolean weighsTheElement = false;
            for (Map.Entry<Quantity, ExactRatio> atom : remainder.dividend().coefs().entrySet()) {
                if (atom.getKey() instanceof DecisionAtom.OfTheInput) {
                    continue;
                }
                if (!(atom.getKey() instanceof Quantity.OfABinding bound)
                        || !(bound.handed().orElse(null) instanceof Quantity.AWholeNumberInTurn)
                        || (element != null && !element.equals(bound))
                        || !atom.getValue().isWhole()) {
                    return false;
                }
                element = bound;
                weighsTheElement = true;
            }
            if (weighsTheElement) {
                every = every.multiply(remainder.divisor())
                        .divide(every.gcd(remainder.divisor()));
            }
            return true;
        }
    }
}
