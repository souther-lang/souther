package souther.compiler.meaning;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.partition.CompositionBudget;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

/**
 * What a comparison of remainders over the element of a list of every whole number between two
 * states on the elements the list starts with, as many of them as the divisors come round in.
 *
 * <p>Those elements are every element there is to read. The element is the list's start and a
 * whole number past it, weighed in each dividend by a whole number, so what each remainder leaves
 * comes round every divisor of elements: an element as many past the start as the divisors come
 * round in, or more, leaves what one of the first ones leaves, and the comparison on it is the
 * comparison on that one, in a list holding that one too. On each of them every dividend is a
 * form of the input's numbers alone, moved by whole turns of its divisor as the remainder of such
 * a form is.
 *
 * <p>Only where every value read off a binding in the comparison is that element, and inside the
 * remainders, where it comes round. That a run makes the comparison on each element the list
 * holds is not said here.
 */
public final class TheWholeNumbersAListStartsWith {

    private TheWholeNumbersAListStartsWith() {
    }

    /** What the comparison comes to on the elements the list starts with. */
    public sealed interface Read {

        /**
         * On each of them, where the list holds it, in order from the start: none for an element
         * on which the comparison holds or fails whatever the row is.
         */
        record OnEach(List<OnOne> each) implements Read {

            public OnEach {
                each = List.copyOf(each);
            }
        }

        /** The divisors come round in more elements than one condition is read on
         *  ({@link CompositionBudget#READINGS_OF_ONE_CONDITION}), and none is read. */
        record PastTheReadings() implements Read {}

        /** The comparison is no such comparison, or the exact arithmetic cannot hold it on some
         *  element. */
        record NotOfThatKind() implements Read {}
    }

    /**
     * The comparison on one element.
     *
     * @param stated  what it states there, a relation of the input's numbers alone
     * @param holding where the list holds that element: its last end at or past it
     */
    public record OnOne(Proposition.Compared stated, Proposition holding) {

        public OnOne {
            Objects.requireNonNull(stated, "the comparison states something on the element");
            Objects.requireNonNull(holding, "and the list holds it somewhere, if only nowhere");
        }
    }

    /** What {@code stated} comes to on the elements the list its element is of starts with. */
    public static Read of(Proposition stated) {
        if (!(stated instanceof Proposition.Compared(Relation.Affine affine, boolean holds,
                Spelling _))) {
            return new Read.NotOfThatKind();
        }
        Quantity.OfABinding element = null;
        BigInteger roundIn = BigInteger.ONE;
        for (Quantity each : affine.form().coefs().keySet()) {
            if (each instanceof Quantity.OfABinding) {
                return new Read.NotOfThatKind();
            }
            if (!(each instanceof Quantity.RemainderOfADividend remainder)
                    || remainder.overTheInput() != null) {
                continue;
            }
            for (Map.Entry<Quantity, ExactRatio> atom : remainder.dividend().coefs().entrySet()) {
                if (atom.getKey() instanceof DecisionAtom.OfTheInput) {
                    continue;
                }
                if (!(atom.getKey() instanceof Quantity.OfABinding bound)
                        || !(bound.handed().orElse(null) instanceof Quantity.AWholeNumberInTurn)
                        || (element != null && !element.equals(bound))
                        || !atom.getValue().isWhole()) {
                    return new Read.NotOfThatKind();
                }
                element = bound;
            }
            roundIn = roundIn.multiply(remainder.divisor())
                    .divide(roundIn.gcd(remainder.divisor()));
        }
        if (element == null
                || !(element.handed().orElseThrow() instanceof Quantity.AWholeNumberInTurn number)) {
            return new Read.NotOfThatKind();
        }
        if (roundIn.compareTo(BigInteger.valueOf(
                CompositionBudget.READINGS_OF_ONE_CONDITION.maximum())) > 0) {
            return new Read.PastTheReadings();
        }
        LinearForm<Quantity> from = ofTheInputsNumbers(number.from());
        LinearForm<Quantity> past = number.to().minus(number.from()).orNull()
                instanceof LinearForm<NumericTerm> gap ? ofTheInputsNumbers(gap) : null;
        if (past == null) {
            return new Read.NotOfThatKind();
        }
        List<OnOne> out = new ArrayList<>();
        for (int at = 0; at < roundIn.intValueExact(); at++) {
            ExactRatio step = ExactRatio.of(at);
            Proposition holding = heldAtOrPast(past, step);
            if (holding instanceof Proposition.Always(boolean some) && !some) {
                break;
            }
            LinearForm<Quantity> there = from.plus(LinearForm.constant(step)).orNull();
            LinearForm<Quantity> on = there == null ? null
                    : withTheElementAt(affine.form(), element, there);
            if (on == null) {
                return new Read.NotOfThatKind();
            }
            if (on.coefs().isEmpty()) {
                continue;
            }
            Relation.OneWay<Quantity> one = Relation.OneWay.of(on, affine.proposition());
            out.add(new OnOne(new Proposition.Compared(
                    new Relation.Affine(one.form(), one.proposition()), holds == one.holds()),
                    holding));
        }
        return new Read.OnEach(out);
    }

    /** {@code form}, a form of the input's numbers, as a form of quantities. */
    private static LinearForm<Quantity> ofTheInputsNumbers(LinearForm<NumericTerm> form) {
        Map<Quantity, ExactRatio> coefs = new LinkedHashMap<>();
        form.coefs().forEach((term, by) -> coefs.put(new DecisionAtom.OfTheInput(term), by));
        return new LinearForm<>(form.constant(), coefs);
    }

    /** That {@code past}, how far a list's end is past its start, is at least {@code step}: that
     *  the list holds the element {@code step} past its start. */
    private static Proposition heldAtOrPast(LinearForm<Quantity> past, ExactRatio step) {
        LinearForm<Quantity> left = past.minus(LinearForm.constant(step)).orNull();
        if (left == null) {
            return new Proposition.Always(false);
        }
        if (left.coefs().isEmpty()) {
            return new Proposition.Always(left.constant().signum() >= 0);
        }
        Relation.OneWay<Quantity> one = Relation.OneWay.of(left, Rel.GE);
        return new Proposition.Compared(new Relation.Affine(one.form(), one.proposition()),
                one.holds());
    }

    /**
     * {@code form} with {@code element} at {@code there} in every remainder it is weighed in — or
     * null where the exact arithmetic cannot hold that. A remainder left with no number of the
     * input in it is the number it leaves.
     */
    private static LinearForm<Quantity> withTheElementAt(LinearForm<Quantity> form,
                                                         Quantity.OfABinding element,
                                                         LinearForm<Quantity> there) {
        List<LinearForm<Quantity>> parts = new ArrayList<>();
        parts.add(LinearForm.constant(form.constant()));
        for (Map.Entry<Quantity, ExactRatio> each : form.coefs().entrySet()) {
            if (!(each.getKey() instanceof Quantity.RemainderOfADividend remainder)
                    || remainder.overTheInput() != null) {
                parts.add(LinearForm.weighing(each.getKey(), each.getValue()));
                continue;
            }
            LinearForm<Quantity> dividend = remainder.dividend().over(atom ->
                    atom.equals(element) ? there : LinearForm.atom(atom));
            if (dividend == null || !dividend.constant().isWhole()
                    || !(dividend.constant().floor() instanceof ExactAnswer.Held<BigInteger>(
                            BigInteger whole))) {
                return null;
            }
            // Moved by a whole turn, a dividend is the dividend it was, as the remainder of a form
            // of the input's numbers is read.
            ExactRatio moved = ExactRatio.of(whole.mod(remainder.divisor()));
            if (!dividend.coefs().isEmpty()) {
                parts.add(LinearForm.weighing(new Quantity.RemainderOfADividend(
                        remainder.operation(), new LinearForm<>(moved, dividend.coefs()),
                        remainder.divisor()), each.getValue()));
                continue;
            }
            LinearForm<Quantity> left = LinearForm.<Quantity>constant(moved)
                    .times(each.getValue()).orNull();
            if (left == null) {
                return null;
            }
            parts.add(left);
        }
        return LinearForm.sum(parts).orNull();
    }
}
