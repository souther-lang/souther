package souther.compiler.values;

import java.util.Objects;
import java.util.Optional;
import java.util.function.Function;

/**
 * What a statement about a member of a container, or about two values being one, is against: the
 * value at a place, which the row writes, or a value the source wrote.
 *
 * <p>A value written is known before any row is. It stands at no place and depends on nothing a
 * row writes, so a reader that needs the value at a place asks {@link #place} and one that needs
 * the value itself reads {@link Written}. The place is whatever the layer names places by — a path
 * of the input, a place a rule reads — and this type says nothing of it.
 *
 * @param <P> how the layer using it names a place
 */
public sealed interface Operand<P> {

    /** The place this is the value at, none where the value is written. */
    Optional<P> place();

    /** This, with the place named as {@code naming} names it — or null where it names none. */
    <Q> Operand<Q> placedAs(Function<? super P, ? extends Q> naming);

    /** The value at {@code place}, which the row writes. */
    record At<P>(P at) implements Operand<P> {

        public At {
            Objects.requireNonNull(at, "the place whose value is meant");
        }

        @Override
        public Optional<P> place() {
            return Optional.of(at);
        }

        /** This itself where the naming leaves the place as it was, so that a reader that tells
         *  many statements the names they stand through makes nothing of the ones it changes
         *  nothing in. */
        @Override
        @SuppressWarnings("unchecked")
        public <Q> Operand<Q> placedAs(Function<? super P, ? extends Q> naming) {
            Q named = naming.apply(at);
            return named == null ? null : named == at ? (Operand<Q>) this : new At<>(named);
        }
    }

    /** The value the source wrote. */
    record Written<P>(Value value) implements Operand<P> {

        public Written {
            Objects.requireNonNull(value, "the value the source wrote");
        }

        @Override
        public Optional<P> place() {
            return Optional.empty();
        }

        @Override
        @SuppressWarnings("unchecked")
        public <Q> Operand<Q> placedAs(Function<? super P, ? extends Q> naming) {
            return (Operand<Q>) this;
        }
    }
}
