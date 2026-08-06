package souther.runtime;

/**
 * The optional type from spec section 7.3: {@code Some(T)} or {@code None}.
 *
 * @param <T> the contained type
 */
public sealed interface Option<T> permits Option.Some, Option.None {

    /** A present value. Its equality is the language's directly rather than the record default: a
     *  {@code Some} is only ever compared with another {@code Some}, so there is no foreign
     *  implementation to disagree with, and what it holds is a Souther value — an amount inside one
     *  is the amount it is at either scale. */
    record Some<T>(T value) implements Option<T> {

        @Override
        public boolean equals(Object o) {
            return o instanceof Some<?> other && Values.equal(value, other.value());
        }

        @Override
        public int hashCode() {
            return Values.hash(value);
        }
    }

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

    /** Bridges the value a Raoh nullable-field decoder lands on to the Souther {@code Option}.
     * Called by generated decode bodies for {@code ?} fields. A {@code ?} field is {@code None} for
     * an absent key and for a written {@code null} alike, and that decoder answers both with a
     * null. */
    static <T> Option<T> ofNullable(T value) {
        return value == null ? none() : new Some<>(value);
    }

    default boolean isPresent() {
        return this instanceof Some<T>;
    }
}
