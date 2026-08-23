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
}
