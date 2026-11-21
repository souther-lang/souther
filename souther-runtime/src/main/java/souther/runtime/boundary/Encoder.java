package souther.runtime.boundary;

import java.util.function.Function;

/**
 * Writes a {@code T} as its external representation, a tree of maps, lists and scalars (spec
 * {@code [#encoder-role]}). A data's derived encoder is its {@code encoder()}. It is total: every
 * value has a representation.
 *
 * @param <T> what is written
 * @param <R> what it is written as
 */
@FunctionalInterface
public interface Encoder<T, R> {

    /** The external representation of {@code value}. */
    R encode(T value);

    /** This encoder, handed what {@code f} makes of a value. */
    default <S> Encoder<S, R> contramap(Function<? super S, ? extends T> f) {
        return value -> encode(f.apply(value));
    }

    /** This encoder, what it writes then written by {@code next}. */
    default <P> Encoder<T, P> andThen(Encoder<? super R, ? extends P> next) {
        return value -> next.encode(encode(value));
    }
}
