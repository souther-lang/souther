package souther.compiler.query;

import souther.compiler.observe.Incompleteness;

import java.util.Collections;
import java.util.EnumSet;
import java.util.Set;

/**
 * What stopped this compiler establishing that a row can be written at a point.
 *
 * <p>Not a reason a row cannot be written. Every case here is a budget of this compiler's own
 * reached on the way to an answer, so what it licenses is that the question is open — and a reader
 * that turned one of these into a statement about the model would be reporting a policy as a
 * property of what somebody wrote.
 *
 * <p><b>Made where the establishing stopped, and never worked out afterwards.</b> The outcome a
 * search comes back with says that nothing came of it; which budget ran out is known only where it
 * ran out, and a reader recovering it from the outcome would be recovering it from something that
 * has already lost it — one reason a search comes back with is written wherever a search can stop,
 * by files that stop for nothing like each other. So a producer that stops hands this over, and one
 * that has nothing to hand over says so by there being no gap rather than by a gap nobody made.
 *
 * <p>One case today. A candidate this compiler declined to compose leaves the same question open
 * for the same kind of reason, and it is not here: what stops that composing is a different budget
 * in a different stage, and the value that would have been read back was never built. A case for it
 * arrives beside this one, and every reader that has to tell them apart is a reader an exhaustive
 * switch already stops.
 */
public sealed interface EstablishmentGap {

    /**
     * An observation of the value did not come back whole, so where it stands could not be read.
     *
     * <p>The value was built and the module's own decoders took it. What did not happen is the
     * reading back, and {@link Incompleteness.Code} is what says whether a limit shortened the
     * observation or nothing could be made of the value at all.
     */
    record Observation(Set<Incompleteness.Code> causes) implements EstablishmentGap {

        public Observation {
            if (causes == null || causes.isEmpty()) {
                throw new IllegalArgumentException(
                        "an observation that stopped something says what stopped it");
            }
            causes = Collections.unmodifiableSet(EnumSet.copyOf(causes));
        }
    }
}
