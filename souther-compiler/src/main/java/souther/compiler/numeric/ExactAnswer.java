package souther.compiler.numeric;

import souther.exact.ExactFailure;

import java.util.function.Function;
import java.util.function.Supplier;

/**
 * What an operation of {@link ExactRatio} comes to: a value, or which of the two ways
 * {@link ExactFailure} left it unheld.
 *
 * <p><b>Not an exception, for the operations reachable from a model's own numbers.</b> A model may
 * write a decimal whose scale sits near the end of the range this compiler holds — squaring a tenth
 * doubles it — and the exact sum of that value and an ordinary one has no representation this host
 * writes. That is not a mistake in the model and not a mistake in this compiler: it is what the sum
 * comes to, and every caller asking the arithmetic for a sum or a difference is asking a question
 * that may have this answer. A caller with no vocabulary for that would either let it end the compile
 * as an internal error, which {@code ExactFailure} being an unchecked exception invites, or would
 * catch it ad hoc at whichever call sites somebody remembered to. This type makes the third answer a
 * caller has to name to get a value out at all, so the compiler finds every place a value is read
 * off one of these.
 *
 * <p>Held by {@link UnheldNumber} and not by {@link ExactFailure} itself, because the two kinds of
 * unheld number are what a caller has a word for and the exception's own message is not.
 */
public sealed interface ExactAnswer<T> {

    record Held<T>(T value) implements ExactAnswer<T> {
        public Held {
            if (value == null) {
                throw new IllegalArgumentException("a held answer holds a value");
            }
        }
    }

    record Unheld<T>(UnheldNumber why) implements ExactAnswer<T> {
        public Unheld {
            if (why == null) {
                throw new IllegalArgumentException("an unheld answer says which way it was unheld");
            }
        }
    }

    static <T> ExactAnswer<T> held(T value) {
        return new Held<>(value);
    }

    static <T> ExactAnswer<T> unheld(UnheldNumber why) {
        return new Unheld<>(why);
    }

    /** {@code attempt}, turned into this: the value where it answered, the failure named where it
     *  did not. */
    static <T> ExactAnswer<T> of(Supplier<T> attempt) {
        try {
            return held(attempt.get());
        } catch (ExactFailure failure) {
            return unheld(UnheldNumber.of(failure));
        }
    }

    /** This value, or {@code null} where none was held.
     *
     *  <p>For a caller whose own sound answer with less is already what {@code null} means there —
     *  an unbounded end, a candidate not composed, a preimage not narrowed. Reaching for this without
     *  checking that first drops which of the two ways the number was unheld, which a caller telling
     *  a reader about it may not be able to spare. */
    default T orNull() {
        return this instanceof Held<T> held ? held.value() : null;
    }

    /** This value as {@code change} makes it, or this way the number was unheld where there is no
     *  value to change. */
    default <R> ExactAnswer<R> map(Function<? super T, ? extends R> change) {
        return switch (this) {
            case Held<T> held -> ExactAnswer.<R>held(change.apply(held.value()));
            case Unheld<T> unheld -> ExactAnswer.<R>unheld(unheld.why());
        };
    }

    /** What {@code next} makes of this value, or this way the number was unheld where there is no
     *  value to make anything of. Which way it was unheld is the first one's, since the second was
     *  never asked. */
    default <R> ExactAnswer<R> flatMap(Function<? super T, ExactAnswer<R>> next) {
        return switch (this) {
            case Held<T> held -> next.apply(held.value());
            case Unheld<T> unheld -> unheld(unheld.why());
        };
    }

    /** This value, or an {@link IllegalStateException} saying {@code because} and which way it was
     *  unheld.
     *
     *  <p>For a caller whose number was asked for earlier, at the one place that can refuse it, so
     *  that reaching an unheld answer here is a defect of that place and not a property of the
     *  model. Never for a number a model's own constants can put past the range. */
    default T orFail(String because) {
        return orFail(() -> because);
    }

    /** The same, with the reason worked out only where it is needed. For a caller whose reason
     *  names the number, which is text nobody should pay for at every call that is held. */
    default T orFail(Supplier<String> because) {
        return switch (this) {
            case Held<T> held -> held.value();
            case Unheld<T> unheld ->
                    throw new IllegalStateException(because.get() + ": " + unheld.why());
        };
    }

    /** Whether this is a value and not a way the arithmetic left the number unheld. */
    default boolean isHeld() {
        return this instanceof Held<T>;
    }
}
