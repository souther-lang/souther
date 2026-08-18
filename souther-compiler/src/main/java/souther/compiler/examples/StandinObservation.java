package souther.compiler.examples;

import souther.compiler.observe.ObservedValue;

/**
 * What the bound implementation answered for a {@link StandinEntry}'s input, held to what the entry
 * states.
 *
 * <p>An observation and not a verdict. A behavior's own recorded row against the implementation is
 * an obligation held to an observation, and {@code evaluate} answers {@code FAILED} for it; a fake
 * entry against the implementation is a stand-in's <em>statement</em> held to an observation, and a
 * disagreement on its own still does not say which side is wrong. ADR-0093 made that disagreement a
 * warning for the same reason, and drew the layer line the same way: the compiler states it and does
 * not choose a side. Whether one fails a build is not knowledge of the model, so no severity and no
 * policy type lives here — a consumer that wants a table held strictly writes a filter.
 *
 * <p>A fake deliberately written to answer what the real dependency cannot — to reach a composite's
 * error path — shows up here as a disagreement. A fake stating a {@code PaymentGatewayDown} no
 * implementation returns is not an imitation that got it wrong; it is the environment the recovery
 * path is given, and disagreeing is what it was written to do.
 */
public sealed interface StandinObservation {

    /** The implementation answered what the entry states. */
    record AsStated() implements StandinObservation {}

    /**
     * The implementation answered, and with something else.
     *
     * <p>Both values, so the two can be read against each other, and then where they part: an answer
     * that wears a name the entry does not differs at one position by its type, which reading two
     * whole values does not say on its own.
     */
    record OtherThanStated(ObservedValue stated, ObservedValue answered, String where)
            implements StandinObservation {}

    /**
     * No two values were compared.
     *
     * <p>This is what keeps {@link OtherThanStated} meaning that two were. A fake stating an answer
     * where the implementation aborts is not a mismatch of values — it is the implementation having
     * no answer for that input, a finding of its own.
     */
    record Unobserved(Reason why) implements StandinObservation {}

    /**
     * How far the observation got.
     *
     * <p>Not {@code FailurePhase}: that vocabulary classifies where a row's evaluation stopped, and
     * this one says why an observation did not come to be. Each carries what it has, so a consumer
     * decides per arm what a test does with it.
     */
    sealed interface Reason {

        /** What it said, for a consumer that shows it. */
        String said();

        /** The implementation was applied and came back with a failure. */
        record TheInvocationAborted(String said) implements Reason {}

        /** What was to apply the behavior could not be reached. */
        record TheImplementationWasNotReached(String said) implements Reason {}

        /** A value this compile built could not be put in the form the implementation reads. */
        record AValueCouldNotCross(String said) implements Reason {}

        /** The entry's own values could not be built, or the observation ran out of what it was
         *  allowed. Nothing was asked of the implementation. */
        record TheEntryWasNotRead(String said) implements Reason {}
    }
}
