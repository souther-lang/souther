package souther.compiler.check;

import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.OrderedInterval;
import souther.compiler.numeric.ValueTransformation;
import souther.compiler.semantics.TakenArguments;
import souther.compiler.semantics.TakenAs;
import souther.compiler.types.ValueName;

/**
 * A number an operation answers of what stands at a place, and never what stands there.
 *
 * <p>{@link NumberAt} says which of the numbers at a place a subject is, and both kinds are one type
 * there because a reader that has to say what two readings of one name came to needs them under one
 * subject. This is the half an operation answers, and it is its own type because one order has one
 * owner: where the values at a position stop is the reading of ends' ({@link OrderedReading}), and
 * how long the string standing there is is another order this reading holds.
 *
 * <p><b>The rule is fixed by what can be built and not by a convention.</b> There is no way to make
 * one of these out of a place's own value — {@link #of} answers with nothing for one — so a reading
 * keyed by these cannot come to hold a range the ends already own. Left as a {@code NumberAt} under
 * a comment, a position's own value put in by mistake would join and meet perfectly happily, and
 * what came out is two mechanisms settling one order and a report answering from whichever ran last.
 *
 * @param position where the number is read from
 * @param operation the operation that answers it, as it resolved. Two spellings reaching one
 *                  operation are one number, and two operations over one place are two
 * @param arguments what the operation was given beside the value at {@code position}, which is part
 *                  of which number this is: two takings differing only there are two numbers, and a
 *                  reading keyed by these without them would hold one order for both
 * @param from      what the value the operation took its number of was made from the one at
 *                  {@code position}: the year of a date and the year of it a day on are two numbers
 */
record DerivedNumber(RuleKey position, ValueName operation, TakenArguments arguments,
                     ValueTransformation from) {

    DerivedNumber {
        if (position == null || operation == null || arguments == null || from == null) {
            throw new IllegalArgumentException("a derived number is what some operation answers"
                    + " of somewhere, with whatever it was given beside that value and whatever"
                    + " the value was made from the one standing there");
        }
    }

    /** The number {@code at} is, or null where it is what stands at the place rather than
     *  something answered of it. */
    static DerivedNumber of(NumberAt<RuleKey> at) {
        return at.of() instanceof NumberAt.OfWhatNumber.OfWhatAnOperationAnswers taken
                ? new DerivedNumber(at.position(), taken.operation(), taken.arguments(),
                        taken.from())
                : null;
    }

    /**
     * Whether the values at {@link #position} are read back out of what the rules leave this number,
     * beyond the counts every position of a counted type has: a part of the date standing there, or
     * its remainder by a divisor that was written.
     *
     * <p>Those are the numbers the reading of a position's values holds a class for
     * ({@link FieldDomains#datePartsAt}, {@link FieldDomains#valueClassAt}). Any other number an
     * operation answers is one nothing turns back into values, and a line on it read as a line on the
     * position would be an account of a rule nobody carried out.
     */
    boolean holdsTheValuesOf() {
        if (!(from instanceof ValueTransformation.Identity)) {
            return false;
        }
        return switch (DefaultBoundOperationFacts.get().takenAs(operation, arguments)) {
            case TakenAs.PartOfDate _ -> arguments.none();
            case TakenAs.TheFloorRemainder remainder -> remainder.settledBy(arguments)
                    && arguments.byPosition().size() == 1;
            case null, default -> false;
        };
    }

    /**
     * Whether the values {@code range} leaves this number are the values the reading of the
     * position holds of it, so that a rule leaving it there is carried out whole.
     *
     * <p>A count of any range is, and so is a part of a date — the days are walked for it. A remainder
     * is only where the range is one number, since what is held of a value is the one class it leaves
     * by the divisor: {@code Int.floorMod(value, 7) >= 3} leaves four classes, and held as one of them
     * or as none it would be a rule read as more or less than it says.
     */
    boolean carriesOut(OrderedInterval range) {
        return switch (DefaultBoundOperationFacts.get().takenAs(operation, arguments)) {
            case TakenAs.HowManyItHolds _, TakenAs.PartOfDate _ -> true;
            case TakenAs.TheFloorRemainder _ ->
                    new NumericDomain.Bounds(range.low(), range.high()).holdsOneWholeNumber() != null;
            case null, default -> false;
        };
    }

    /** The same number as the subject every other reader knows it by. */
    NumberAt<RuleKey> asNumber() {
        return NumberAt.takenOf(position, operation, arguments, from);
    }

    @Override
    public String toString() {
        return operation + arguments.writtenWith(from.writtenAround(position.toString()));
    }
}
