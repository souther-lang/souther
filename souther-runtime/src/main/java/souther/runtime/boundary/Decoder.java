package souther.runtime.boundary;

import org.jspecify.annotations.Nullable;
import souther.runtime.Result;

import java.util.function.Function;

/**
 * Reads an external representation as a {@code T}, or answers the refusals of what it could not read
 * (spec {@code [#decoder-role]}). A data's derived decoder is its {@code decoder()}.
 *
 * <p>The input is read through a {@link TreeReader}: {@link #decode(Object)} reads maps, lists and
 * the JDK's values, and {@link #decode(Object, TreeReader)} another tree.
 *
 * @param <T> what a decode answers
 */
@FunctionalInterface
public interface Decoder<T> {

    /** Reads {@code node}, which stands at {@code path} of the input, through {@code reader}. */
    Result<T, Refusals> decode(@Nullable Object node, Path path, TreeReader reader);

    /** Reads maps, lists and the JDK's values. */
    default Result<T, Refusals> decode(@Nullable Object input) {
        return decode(input, Path.ROOT, TreeReader.PLAIN);
    }

    /** Reads another tree, through its reader. */
    default Result<T, Refusals> decode(@Nullable Object input, TreeReader reader) {
        return decode(input, Path.ROOT, reader);
    }

    /** This decoder, its value then put through {@code f}. */
    default <U> Decoder<U> map(Function<? super T, ? extends U> f) {
        return (node, path, reader) -> switch (decode(node, path, reader)) {
            case Result.Ok<T, Refusals>(T value) -> Result.ok(f.apply(value));
            case Result.Err<T, Refusals>(Refusals refusals) -> Result.err(refusals);
        };
    }

    /** This decoder, its value then read again by {@code next} at the same path: a step that can
     *  itself refuse. */
    default <U> Decoder<U> then(Step<? super T, U> next) {
        return (node, path, reader) -> switch (decode(node, path, reader)) {
            case Result.Ok<T, Refusals>(T value) -> next.apply(value, path);
            case Result.Err<T, Refusals>(Refusals refusals) -> Result.err(refusals);
        };
    }

    /** A step after a decode: the value read, and the path it was read at. */
    @FunctionalInterface
    interface Step<T, U> {
        Result<U, Refusals> apply(T value, Path path);
    }
}
