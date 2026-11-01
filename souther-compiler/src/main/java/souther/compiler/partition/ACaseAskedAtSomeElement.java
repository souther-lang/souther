package souther.compiler.partition;

import souther.compiler.check.ElementsWrittenOut;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Quantities;
import souther.compiler.meaning.OnOneElement;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Rel;
import souther.compiler.numeric.UnheldNumber;

import java.math.BigInteger;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

/**
 * A case a line decides in that weighs the element of a list of every whole number between two
 * ({@link OnOneElement}), asked whether it holds at a row with the element at some value the
 * row's list holds: each value put in the case, and the case then asked of the row as one of the
 * input's numbers alone ({@link AStatementAtARow}).
 *
 * <p>Every value from the list's start to its end at the row, up to
 * {@link ElementsWrittenOut#MOST_WALKED} of them, and of a turn the case holds the element to come
 * round to only the values of that turn — the first alone where the case comes out alike on all
 * of them. A list holding more, with no value tried holding it, is one this could not tell of:
 * the values left are not values it fails at. One value the case could not be told at is said
 * the same way, unless another holds it. The element is the same one wherever the case weighs it,
 * so a row holding it is one on which every part of the case is read at one element.
 *
 * <p>Held by whoever puts the case to rows, beside the case as it stands, and by nothing an answer
 * carries: it keeps the reading of the input it puts each value's case to rows with, and the case
 * at each value it has tried.
 */
final class ACaseAskedAtSomeElement {

    private final Proposition stated;
    private final Quantity.OfABinding element;
    /** The part holding the element to come round to one value in turns of {@link #every}
     *  ({@link #turnIn}), or null where none does and every value is one of a turn. */
    private final Proposition.Compared turn;
    private final BigInteger every;
    /** Whether the case comes out alike on every value of a turn
     *  ({@link OnOneElement#comesOutAlikeEvery}), so that the first the list holds answers. */
    private final boolean onceATurn;
    private final String behavior;
    private final Quantities quantities;
    /** The relations read so far over {@link #quantities}, for each value's case to share. */
    private final Map<AStatementAtARow.RelationRead, AStatementAtARow.OneRelation> read;
    /** The case with the element at each value tried so far, read to be put to rows, or nothing
     *  where the element cannot be put there: one whichever row asks it. */
    private final Map<BigInteger, Optional<AStatementAtARow>> atValue = new ConcurrentHashMap<>();
    /** The same of {@link #turn}. */
    private final Map<BigInteger, Optional<AStatementAtARow>> atTurn = new ConcurrentHashMap<>();

    private ACaseAskedAtSomeElement(Proposition stated, Quantity.OfABinding element,
                                    String behavior, Quantities quantities,
                                    Map<AStatementAtARow.RelationRead,
                                            AStatementAtARow.OneRelation> read) {
        this.stated = stated;
        this.element = element;
        this.turn = turnIn(stated, element);
        this.every = turn == null ? BigInteger.ONE
                : ((Quantity.RemainderOfADividend) ((Relation.Affine) turn.relation()).form()
                        .coefs().keySet().iterator().next()).divisor();
        this.onceATurn = OnOneElement.comesOutAlikeEvery(stated, element)
                .filter(every::equals).isPresent();
        this.behavior = behavior;
        this.quantities = quantities;
        this.read = read;
    }

    /** {@code stated} asked at some element — or nothing where it weighs no such element and is
     *  asked as it stands. */
    static Optional<ACaseAskedAtSomeElement> of(Proposition stated, String behavior,
                                                Quantities quantities,
                                                Map<AStatementAtARow.RelationRead,
                                                        AStatementAtARow.OneRelation> read) {
        return OnOneElement.theElementOf(stated).map(element ->
                new ACaseAskedAtSomeElement(stated, element, behavior, quantities, read));
    }

    /**
     * The part of {@code stated} holding {@code element} to come round to one value, every other
     * part beside it ({@link OnOneElement#comesRoundTo}): a remainder the element is weighed in
     * once, said to leave nothing — or null where it holds no such part.
     */
    private static Proposition.Compared turnIn(Proposition stated, Quantity.OfABinding element) {
        List<Proposition> each = stated instanceof Proposition.All all ? all.parts()
                : List.of(stated);
        for (Proposition part : each) {
            if (part instanceof Proposition.All) {
                Proposition.Compared inside = turnIn(part, element);
                if (inside != null) {
                    return inside;
                }
            }
            if (part instanceof Proposition.Compared compared && compared.holds()
                    && compared.relation() instanceof Relation.Affine affine
                    && affine.proposition() == Rel.EQ
                    && affine.form().constant().signum() == 0
                    && affine.form().coefs().size() == 1
                    && affine.form().coefs().keySet().iterator().next()
                            instanceof Quantity.RemainderOfADividend remainder
                    && remainder.dividend().coefs().get(element) instanceof ExactRatio weight
                    && weight.abs().equals(ExactRatio.ONE)) {
                return compared;
            }
        }
        return null;
    }

    /** Whether the case holds at {@code row} with the element at some value the row's list
     *  holds. */
    AStatementAtARow.Answer at(BorderQuantity.Observation row) {
        Quantity.AWholeNumberInTurn number =
                (Quantity.AWholeNumberInTurn) element.handed().orElseThrow();
        Set<ReadingGap> why = new LinkedHashSet<>();
        BigInteger from = valueAt(number.from(), row, why);
        BigInteger to = valueAt(number.to(), row, why);
        if (from == null || to == null) {
            return new AStatementAtARow.Answer.CouldNotTell(why);
        }
        // Where the case holds the element to come round to one value in turns of a divisor,
        // only the values it comes round to are tried: the first of them is among as many values
        // from the start as the divisor, and each next is a turn past it.
        BigInteger start = null;
        for (BigInteger value = from; start == null && value.compareTo(to) <= 0
                && value.compareTo(from.add(every)) < 0; value = value.add(BigInteger.ONE)) {
            AStatementAtARow there = turn == null ? null : putAt(atTurn, turn, value);
            AStatementAtARow.Answer turned = turn == null ? AStatementAtARow.Answer.HOLDS
                    : there == null ? new AStatementAtARow.Answer.CouldNotTell(Set.of(
                            ReadingGap.of(UnheldNumber.NO_REPRESENTATION_EXISTS)))
                    : there.at(row);
            switch (turned) {
                case AStatementAtARow.Answer.Holds _ -> start = value;
                case AStatementAtARow.Answer.Fails _ -> { }
                case AStatementAtARow.Answer.CouldNotTell(var stopped) -> {
                    why.addAll(stopped);
                    return new AStatementAtARow.Answer.CouldNotTell(why);
                }
            }
        }
        if (start == null) {
            return AStatementAtARow.Answer.FAILS;
        }
        int tried = 0;
        for (BigInteger value = start; value.compareTo(to) <= 0; value = value.add(every)) {
            if (onceATurn && tried == 1) {
                break;
            }
            if (tried++ == ElementsWrittenOut.MOST_WALKED) {
                why.add(new ReadingGap.ReachNotRead(
                        ReadingGap.ReachNotRead.Why.MORE_ELEMENTS_THAN_ARE_WRITTEN_OUT));
                break;
            }
            AStatementAtARow there = putAt(atValue, stated, value);
            if (there == null) {
                why.add(ReadingGap.of(UnheldNumber.NO_REPRESENTATION_EXISTS));
                continue;
            }
            switch (there.at(row)) {
                case AStatementAtARow.Answer.Holds _ -> {
                    return AStatementAtARow.Answer.HOLDS;
                }
                case AStatementAtARow.Answer.Fails _ -> { }
                case AStatementAtARow.Answer.CouldNotTell(var stopped) -> why.addAll(stopped);
            }
        }
        return why.isEmpty() ? AStatementAtARow.Answer.FAILS
                : new AStatementAtARow.Answer.CouldNotTell(why);
    }

    /** {@code part} with the element at {@code value}, read to be put to rows and kept in
     *  {@code kept} — or null where the element cannot be put there. */
    private AStatementAtARow putAt(Map<BigInteger, Optional<AStatementAtARow>> kept,
                                   Proposition part, BigInteger value) {
        return kept.computeIfAbsent(value, at ->
                Optional.ofNullable(OnOneElement.at(part, element,
                        LinearForm.constant(ExactRatio.of(at))))
                        .map(one -> AStatementAtARow.readBy(one, behavior, quantities, read)))
                .orElse(null);
    }

    /** The whole number {@code form} comes to at {@code row} — or null, with why put in
     *  {@code why}, where it could not be read or is no whole number. */
    private BigInteger valueAt(LinearForm<NumericTerm> form, BorderQuantity.Observation row,
                               Set<ReadingGap> why) {
        ExactAnswer<ExactRatio> sum;
        if (form.coefs().isEmpty()) {
            sum = ExactAnswer.held(form.constant());
        } else {
            LinearQuantity over = Cutting.readAt(behavior, form, quantities);
            if (over == null) {
                why.add(ReadingGap.of(UnheldNumber.NO_REPRESENTATION_EXISTS));
                return null;
            }
            switch (over.valuesOf(over.read(row))) {
                case ValuesAtARow.Read(Map<NumericTerm, Place> values) ->
                        sum = OrderedAffineBoundary.at(form, values);
                case ValuesAtARow.CouldNotTell(var stopped) -> {
                    why.addAll(stopped);
                    return null;
                }
                case ValuesAtARow.NoneHere _ -> {
                    why.add(ReadingGap.NO_VALUE);
                    return null;
                }
            }
        }
        return switch (sum) {
            case ExactAnswer.Held<ExactRatio>(ExactRatio held) when held.isWhole()
                    && held.floor() instanceof ExactAnswer.Held<BigInteger>(BigInteger whole) ->
                    whole;
            case ExactAnswer.Held<ExactRatio> _ -> {
                why.add(ReadingGap.NO_VALUE);
                yield null;
            }
            case ExactAnswer.Unheld<ExactRatio> unheld -> {
                why.add(ReadingGap.of(unheld.why()));
                yield null;
            }
        };
    }
}
