package souther.compiler.partition;

import souther.compiler.inputs.TermPath;
import souther.compiler.values.Value;

import java.util.Objects;
import java.util.Optional;
import java.util.Set;

/**
 * What a container is asked to hold, or not to hold, as an element or as a key: the value at a
 * position of the row, or a value the source wrote.
 *
 * <p>A value at a position is one the row chooses, so it is handed to the container once the row
 * has chosen it, and what chooses it is part of the demand. A value written is known before any
 * row is: it stands at no position and depends on nothing a row writes, so it is handed as it is.
 */
sealed interface MembershipTarget {

    /** The positions of the row this names, none where the value is written. */
    Set<TermPath> positions();

    /** The position this is the value at, where it is one. */
    Optional<TermPath> position();

    /** The value at {@code at}, which the row writes. */
    record AtPosition(TermPath at) implements MembershipTarget {

        public AtPosition {
            Objects.requireNonNull(at, "the position whose value is asked");
        }

        @Override
        public Set<TermPath> positions() {
            return Set.of(at);
        }

        @Override
        public Optional<TermPath> position() {
            return Optional.of(at);
        }
    }

    /** The value the source wrote, which stands at no position. */
    record Written(Value value) implements MembershipTarget {

        public Written {
            Objects.requireNonNull(value, "the value the source wrote");
        }

        @Override
        public Set<TermPath> positions() {
            return Set.of();
        }

        @Override
        public Optional<TermPath> position() {
            return Optional.empty();
        }
    }
}
