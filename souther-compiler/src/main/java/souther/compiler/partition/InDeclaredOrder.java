package souther.compiler.partition;

import java.util.Collection;
import java.util.Collections;
import java.util.EnumSet;
import java.util.Set;

/**
 * A set of an enumeration's constants, held in the order they are declared in.
 *
 * <p>For a set kept in a value that goes into an answer: a set copied any other way iterates in an
 * order each run picks, and a report reading it says what it holds in that order.
 */
final class InDeclaredOrder {

    private InDeclaredOrder() {
    }

    /** {@code these}, held in the order they are declared in. */
    static <E extends Enum<E>> Set<E> of(Collection<E> these) {
        return these.isEmpty() ? Set.of() : Collections.unmodifiableSet(EnumSet.copyOf(these));
    }
}
