package souther.runtime;

/**
 * The optional type from spec section 7.3: {@code Some(T)} or {@code None}.
 *
 * @param <T> the contained type
 */
public sealed interface Option<T> permits Option.Some, Option.None {

    record Some<T>(T value) implements Option<T> {}

    record None<T>() implements Option<T> {}

    /** The one absent value. {@code None} is a component-less record, so every instance is equal to
     *  every other and carries nothing of {@code T} — one erased instance serves every element type,
     *  as {@code Collections.emptyList()} does. */
    None<?> NONE = new None<>();

    static <T> Option<T> some(T value) {
        return new Some<>(value);
    }

    @SuppressWarnings("unchecked")
    static <T> Option<T> none() {
        return (Option<T>) NONE;
    }

    /** Bridges a {@code java.util.Optional} (as produced by a Raoh optional-field decoder) to
     * the Souther {@code Option}. Called by generated decode bodies for {@code ?} fields. */
    static <T> Option<T> ofOptional(java.util.Optional<T> o) {
        return o.isPresent() ? new Some<>(o.get()) : none();
    }

    default boolean isPresent() {
        return this instanceof Some<T>;
    }
}
