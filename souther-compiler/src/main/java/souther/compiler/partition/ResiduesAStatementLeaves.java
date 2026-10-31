package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.OnOneElement;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.numeric.WholeNumberRuns;

import java.math.BigInteger;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * Which remainders of one form by one divisor a statement can hold at: every remainder a row
 * meeting the statement leaves, and perhaps more.
 *
 * <p>Read part by part. A comparison of what a division by the same divisor leaves of the same
 * form, moved by a constant, against a number holds at exactly the remainders it names, turned
 * round the divisor by the constant — said not to hold, at exactly the others. Parts held together
 * hold where all of them may, and parts any one of which is enough where any of them may. Anything
 * else holds at every remainder: what it says is left for the row to be read against, and taken
 * as holding anywhere it never turns away a row that meets the statement. A part is never turned
 * round unless where it holds was read exactly, which only a comparison of the remainder is.
 *
 * <p>Where the statement holds the element of a list of whole numbers to come round to one value
 * in turns of a multiple of the divisor ({@link OnOneElement#comesRoundTo}), every row meeting it
 * is at such an element, so a remainder of the form and that element is the remainder of the form
 * moved by what the element leaves.
 */
final class ResiduesAStatementLeaves {

    private ResiduesAStatementLeaves() {
    }

    /** The remainders by {@code divisor} of {@code dividend} at which {@code stated} may hold. */
    static WholeNumberRuns of(Proposition stated, LinearForm<NumericTerm> dividend,
                              BigInteger divisor) {
        if (!dividend.constant().isWhole()) {
            return WholeNumberRuns.EVERY;
        }
        return new Reading(dividend, divisor, turnIn(stated, divisor)).held(stated);
    }

    /** An element of a list of whole numbers a statement holds to come round, and what it leaves
     *  by the divisor. */
    private record ComesRound(Quantity.OfABinding element, BigInteger leaves) {}

    /** What {@code stated} holds its element to come round to, as a part of what it holds
     *  together, in turns of a multiple of {@code divisor} — or null where it holds no such part. */
    private static ComesRound turnIn(Proposition stated, BigInteger divisor) {
        Optional<Quantity.OfABinding> element = OnOneElement.theElementOf(stated);
        if (element.isEmpty()) {
            return null;
        }
        List<Proposition> each = stated instanceof Proposition.All all ? all.parts()
                : List.of(stated);
        for (Proposition part : each) {
            if (part instanceof Proposition.Compared compared && compared.holds()
                    && compared.relation() instanceof Relation.Affine affine
                    && affine.proposition() == Rel.EQ
                    && affine.form().constant().signum() == 0
                    && affine.form().coefs().size() == 1
                    && affine.form().coefs().keySet().iterator().next()
                            instanceof Quantity.RemainderOfADividend remainder
                    && remainder.dividend().coefs().size() == 1
                    && ExactRatio.ONE.equals(remainder.dividend().coefs().get(element.get()))
                    && remainder.divisor().mod(divisor).signum() == 0
                    && remainder.dividend().constant().isWhole()) {
                return new ComesRound(element.get(),
                        whole(remainder.dividend().constant()).negate().mod(divisor));
            }
        }
        return null;
    }

    private record Reading(LinearForm<NumericTerm> dividend, BigInteger divisor,
                           ComesRound round) {

        WholeNumberRuns held(Proposition stated) {
            return switch (stated) {
                case Proposition.Always(boolean holds) ->
                        holds ? WholeNumberRuns.EVERY : WholeNumberRuns.NONE;
                case Proposition.All(var parts, var _) -> {
                    WholeNumberRuns at = WholeNumberRuns.EVERY;
                    for (Proposition part : parts) {
                        at = at.and(held(part));
                    }
                    yield at;
                }
                case Proposition.Any(var parts, var _) -> {
                    WholeNumberRuns at = WholeNumberRuns.NONE;
                    for (Proposition part : parts) {
                        at = at.or(held(part));
                    }
                    yield at;
                }
                case Proposition.WhereItAnswers(var answers, var states, var _) ->
                        held(answers).and(held(states));
                case Proposition.Compared compared -> ofAComparison(compared);
                default -> WholeNumberRuns.EVERY;
            };
        }

        /** A comparison of one remainder of this form, moved, against a number: exactly the
         *  remainders it names, or the others where it is said not to hold. Anything else: every
         *  remainder. */
        private WholeNumberRuns ofAComparison(Proposition.Compared compared) {
            if (!(compared.relation() instanceof Relation.Affine affine)
                    || affine.form().coefs().size() != 1
                    || !(affine.form().coefs().keySet().iterator().next()
                            instanceof Quantity.RemainderOfADividend remainder)
                    || !remainder.divisor().equals(divisor)) {
                return WholeNumberRuns.EVERY;
            }
            BigInteger moved = movedBy(remainder.dividend());
            ExactRatio weight = affine.form().coefs().values().iterator().next();
            if (moved == null || !(affine.form().constant().negated().dividedBy(weight)
                    instanceof ExactAnswer.Held<ExactRatio>(ExactRatio level))) {
                return WholeNumberRuns.EVERY;
            }
            WholeNumberRuns standing = WholeNumberRuns.standing(
                    weight.signum() > 0 ? affine.proposition() : affine.proposition().turned(),
                    level);
            if (standing == null) {
                return WholeNumberRuns.EVERY;
            }
            WholeNumberRuns left = (compared.holds() ? standing : standing.others())
                    .and(Standing.OfARemainderAndAForm.every(divisor));
            return Standing.OfARemainder.turnedBack(left, moved, divisor);
        }

        /**
         * How far the remainder of {@code other} is past the remainder of this form, where the two
         * are one form moved by a constant — the element counted at what it leaves, where the
         * statement holds it to come round — or null where they are not.
         */
        private BigInteger movedBy(LinearForm<Quantity> other) {
            if (!other.constant().isWhole()) {
                return null;
            }
            BigInteger moved = whole(other.constant()).subtract(whole(dividend.constant()));
            int matched = 0;
            for (Map.Entry<Quantity, ExactRatio> each : other.coefs().entrySet()) {
                if (round != null && each.getKey().equals(round.element())) {
                    if (!ExactRatio.ONE.equals(each.getValue())) {
                        return null;
                    }
                    moved = moved.add(round.leaves());
                    continue;
                }
                if (!(each.getKey() instanceof DecisionAtom.OfTheInput(NumericTerm term))
                        || !each.getValue().equals(dividend.coefs().get(term))) {
                    return null;
                }
                matched++;
            }
            return matched == dividend.coefs().size() ? moved : null;
        }
    }

    private static BigInteger whole(ExactRatio ratio) {
        return ((ExactAnswer.Held<BigInteger>) ratio.floor()).value();
    }
}
