package souther.compiler.meaning;

import souther.compiler.inputs.NumericTerm;
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
import java.util.Optional;

/**
 * What a comparison of remainders over the element of a list of every whole number between two
 * states on the elements the list starts with, as many of them as the statement comes round in.
 *
 * <p>Those elements are every element there is to read. Where the statement comes round
 * ({@link TheElementComesRound}), an element as many past the start as it comes round in, or
 * more, makes it come out as on one of the first ones, in a list holding that one too. On each of
 * them every dividend is a form of the input's numbers alone, moved by whole turns of its divisor
 * as the remainder of such a form is, and the relations are held together as the statement holds
 * them. Where only its remainders come round ({@link TheElementComesRound#inItsRemainders}), the
 * rest of the statement keeps the element, and is asked of a row at an element that comes round
 * to the one it is read on.
 *
 * <p>That a run makes the comparison on each element the list holds is not said here.
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
     * @param stated  what it states there, relations of the input's numbers alone, held together
     *                as they are in the comparison
     * @param holding where the list holds that element, its last end at or past it, and the
     *                element is one coming round to it ({@link OnOneElement#comesRoundTo}): what
     *                else a run states of the element there is then stated of one it comes out
     *                the same on
     */
    public record OnOne(Proposition stated, Proposition holding) {

        public OnOne {
            Objects.requireNonNull(stated, "the comparison states something on the element");
            Objects.requireNonNull(holding, "and the list holds it somewhere, if only nowhere");
        }
    }

    /** What {@code stated} comes to on the elements the list its element is of starts with. */
    public static Read of(Proposition stated) {
        return planFor(stated).on(stated);
    }

    /**
     * How the comparison {@code whole} is read on the elements its list starts with, worked out
     * once: which elements, and whether the element is put everywhere it is weighed or only inside
     * remainders. A part of {@code whole} is read as the whole is by {@link Plan#on}, so what a
     * part comes to on each element is what it contributes to what the whole comes to there.
     */
    public static Plan planFor(Proposition whole) {
        Optional<TheElementComesRound> round = TheElementComesRound.in(whole);
        boolean everywhere = round.isPresent();
        if (!everywhere) {
            round = TheElementComesRound.inItsRemainders(whole);
        }
        if (round.isEmpty()) {
            return new Plan(new Read.NotOfThatKind(), null, false, null, null);
        }
        if (round.get().every().compareTo(BigInteger.valueOf(
                CompositionBudget.READINGS_OF_ONE_CONDITION.maximum())) > 0) {
            return new Plan(new Read.PastTheReadings(), null, false, null, null);
        }
        Quantity.AWholeNumberInTurn number = round.get().number();
        LinearForm<Quantity> past = number.to().minus(number.from()).orNull()
                instanceof LinearForm<NumericTerm> gap ? ofTheInputsNumbers(gap) : null;
        if (past == null) {
            return new Plan(new Read.NotOfThatKind(), null, false, null, null);
        }
        return new Plan(null, round.get(), everywhere, ofTheInputsNumbers(number.from()), past);
    }

    /** A comparison's reading on the elements its list starts with, from {@link #planFor}. */
    public static final class Plan {

        private final Read refused;
        private final TheElementComesRound round;
        private final boolean everywhere;
        private final LinearForm<Quantity> from;
        private final LinearForm<Quantity> past;

        private Plan(Read refused, TheElementComesRound round, boolean everywhere,
                     LinearForm<Quantity> from, LinearForm<Quantity> past) {
            this.refused = refused;
            this.round = round;
            this.everywhere = everywhere;
            this.from = from;
            this.past = past;
        }

        /** What {@code part} comes to on each of those elements: the whole's own, where
         *  {@code part} is the whole. */
        public Read on(Proposition part) {
            if (refused != null) {
                return refused;
            }
            Quantity.OfABinding element = round.element();
            List<OnOne> out = new ArrayList<>();
            for (int at = 0; at < round.every().intValueExact(); at++) {
                ExactRatio step = ExactRatio.of(at);
                Proposition holding = heldAtOrPast(past, step);
                if (holding instanceof Proposition.Always(boolean some) && !some) {
                    break;
                }
                LinearForm<Quantity> there = from.plus(LinearForm.constant(step)).orNull();
                Proposition on = there == null ? null
                        : everywhere ? OnOneElement.at(part, element, there)
                        : OnOneElement.inItsRemainders(part, element, there);
                if (on == null) {
                    return new Read.NotOfThatKind();
                }
                if (on instanceof Proposition.Always) {
                    continue;
                }
                out.add(new OnOne(on, Proposition.all(List.of(holding,
                        OnOneElement.comesRoundTo(round, at)))));
            }
            return new Read.OnEach(out);
        }
    }

    /** {@code form}, a form of the input's numbers, as a form of quantities. */
    static LinearForm<Quantity> ofTheInputsNumbers(LinearForm<NumericTerm> form) {
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
}
