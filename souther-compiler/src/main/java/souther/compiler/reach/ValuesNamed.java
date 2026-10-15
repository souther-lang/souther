package souther.compiler.reach;

import souther.compiler.values.Value;
import souther.compiler.values.ValueSet;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

/**
 * The values a position's rules name for it, as a proof says them: the ones it may hold, or the
 * ones it may not.
 *
 * <p>Two of the shapes a {@link ValueSet} takes and not the third. A pattern is a machine, which a
 * proof can neither say in a sentence nor be compared by — and a proof is an answer, compared by
 * its value wherever a question is answered again. Held as a {@code ValueSet}, the pattern would be
 * a shape this could carry and nothing could read.
 */
public sealed interface ValuesNamed {

    /** The values the position may hold, and no others — in the order the set holds them, which
     *  is the order a sentence lists them in. */
    record Held(Set<Value> values) implements ValuesNamed {

        public Held {
            if (values.isEmpty()) {
                throw new IllegalArgumentException("a position holding nothing is no value named");
            }
            values = Collections.unmodifiableSet(new LinkedHashSet<>(values));
        }
    }

    /** The values the position may not hold, any other being one it may — in the same order. */
    record Refused(Set<Value> values) implements ValuesNamed {

        public Refused {
            if (values.isEmpty()) {
                throw new IllegalArgumentException("refusing nothing names no value");
            }
            values = Collections.unmodifiableSet(new LinkedHashSet<>(values));
        }
    }

    /** What {@code admitted} names, or null where it names nothing a proof can say — every value,
     *  none, or a pattern. */
    static ValuesNamed of(ValueSet admitted) {
        return switch (admitted) {
            case ValueSet.Finite finite when !finite.values().isEmpty() ->
                    new Held(finite.values());
            case ValueSet.Cofinite cofinite when !cofinite.excluded().isEmpty() ->
                    new Refused(cofinite.excluded());
            case ValueSet.Finite _, ValueSet.Cofinite _, ValueSet.Matching _ -> null;
        };
    }
}
