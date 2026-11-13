package souther.compiler.partition;

import souther.compiler.core.Core;
import souther.compiler.inputs.InputReads;

import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.Map;
import java.util.Optional;
import java.util.function.Supplier;

/**
 * The numbers the value a name is bound to comes to at a reading, kept with the input that is
 * read, for every reading of it.
 *
 * <p>A reading of a comparison is made for each statement of a body that has one, and the names a
 * chain of bindings gives to values made of one another are the same names in each. A value and
 * the reading it is read at is one question whichever statement asks it, and asked afresh by each,
 * a chain of {@code n} names is read {@code n} times over. Kept here, it is read once.
 *
 * <p>Only an answer that was worked out without spending any of the readings the figures allow is
 * kept: one that was cut short by a figure is what the reading that spent it would not give
 * another. That the numbers are not known is kept, as the numbers are.
 */
final class RangesOfNames {

    private final Map<Core, Map<InputReads, Optional<FormRange>>> held =
            Collections.synchronizedMap(new IdentityHashMap<>());

    /**
     * What {@code value} comes to read at {@code at}, taken from an answer kept for that value
     * and that reading where there is one, and otherwise made by {@code fresh}.
     */
    FormRange of(Core value, InputReads at, Supplier<Pullback.Spendless<FormRange>> fresh) {
        Map<InputReads, Optional<FormRange>> atThisValue = held.computeIfAbsent(value,
                _ -> Collections.synchronizedMap(new IdentityHashMap<>()));
        Optional<FormRange> kept = atThisValue.get(at);
        if (kept != null) {
            return kept.orElse(null);
        }
        Pullback.Spendless<FormRange> worked = fresh.get();
        if (worked.spentNothing()) {
            atThisValue.put(at, Optional.ofNullable(worked.value()));
        }
        return worked.value();
    }
}
