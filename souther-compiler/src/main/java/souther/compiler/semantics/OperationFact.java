package souther.compiler.semantics;

/**
 * One thing that is true of one of the language's operations.
 *
 * <p>Kinds are kept apart because they are different statements, not because a reader wants them
 * apart. That an operation answers the number it was given, that it moves a value by an amount, and
 * that the sign of its answer states which of its arguments is the greater are three propositions,
 * and one operation may carry several: {@code Date.addDays} both answers a date shifted by its
 * amount and states how far the two stand apart. Folded into one case per operation, a fact could
 * only be added by widening whatever case was already there.
 *
 * <p>Sealed, so the procedures that hold these to the library's declarations answer for a kind
 * added rather than passing over it.
 */
public sealed interface OperationFact {

    /**
     * The result is the number an argument already is, and this says which argument.
     *
     * <p>Such a call is read into the form its argument has rather than given an atom of its own, so
     * a rule about the argument settles one about the call. {@code Decimal.fromInt(n)} is the one
     * the library has: every {@code Int} is a {@code Decimal} exactly, and the widening states
     * nothing of its own.
     *
     * <p>Not a choice among arguments. What a choice answers is one of two values, decided by the
     * arguments, and which one it is has to be reasoned about case by case; this answers one value
     * unconditionally, in another type. Read as a choice with one candidate, every value-preserving
     * conversion would be filed under selection, and the two stop being one question the moment the
     * library gains a conversion that is not a widening.
     */
    record AnswersItsArgument(ArgumentRef argument) implements OperationFact {

        public AnswersItsArgument {
            java.util.Objects.requireNonNull(argument, "this one names an argument");
        }
    }

    /**
     * The sign of what the operation answers states which of its two arguments is the greater.
     *
     * <p>Zero states the equality and a negative answer the relation the other way, so one of these
     * is the whole of what such an operation says about the pair. Which relation a rule writing one
     * states then follows from where the sign stands against zero and from nothing else.
     *
     * <p>The direction is not the same for all of them: {@code compare(a, b)} is positive where
     * {@code a} is the greater, and {@code daysBetween(from, to)} counts forward from its first
     * argument, so it is positive where the second one is.
     */
    record StatesTheOrderOfItsArguments(PositiveOrder order) implements OperationFact {

        public StatesTheOrderOfItsArguments {
            java.util.Objects.requireNonNull(order, "this one says which way round");
        }
    }

    /**
     * The operation answers the value at {@code of} moved by {@code amount}, and how far it moved is
     * {@code per} of what {@code measure} counts.
     *
     * <p>What a shift states is not a bound on what it answers — a date is not a number — so it is
     * written in the one language there is about such values, which is the number a measure answers
     * of two of them. That number is what a rule over a pair of dates is written in as well, so the
     * two meet without either being restated.
     */
    record ShiftsBy(souther.compiler.types.ValueName.Stdlib measure, ArgumentRef of,
                    ArgumentRef amount, java.math.BigDecimal per) implements OperationFact {

        public ShiftsBy {
            java.util.Objects.requireNonNull(measure, "a shift is stated through a measure");
            java.util.Objects.requireNonNull(of, "and moves something");
            java.util.Objects.requireNonNull(amount, "by something");
            java.util.Objects.requireNonNull(per, "at some rate");
        }
    }

    /**
     * Something that holds of the number the operation answers, wherever it is called.
     *
     * <p>One fact per bound rather than a list in one: an operation with two bounds carries two
     * statements, and they are added and read one at a time.
     */
    record BoundsItsResult(ResultBound bound) implements OperationFact {

        public BoundsItsResult {
            java.util.Objects.requireNonNull(bound, "this one states a bound");
        }
    }

    /**
     * The operation builds a container out of another, and this says where its elements came from
     * and how many of them there are.
     */
    record BuildsItsResultFrom(BuiltFrom built) implements OperationFact {

        public BuildsItsResultFrom {
            java.util.Objects.requireNonNull(built, "this one says what it was built from");
        }
    }
}
