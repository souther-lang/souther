package souther.compiler.inputs;

import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.ObservedValue;

/**
 * What one class makes of one value: it holds it, it does not, or it could not tell.
 *
 * <p>The third is why this is not a {@code boolean}. A class is told from a value by a classifier
 * that may read through it — a number at a position is the number inside the newtype named there,
 * and the walk that finds positions never steps into one — so a classifier is entitled to decode,
 * and decoding can fail. Answered as a yes or a no, a value it could not read comes back as a value
 * it does not hold, and whoever has to say why the row could not be placed has neither the reason
 * nor the knowledge to work one out.
 *
 * <p>The rule is the interpreter's: what read the value says why it could not.
 */
public sealed interface Membership {

    /** The class holds this value. */
    record Match() implements Membership {}

    /** The class does not hold it, which is an answer about a value that was read. */
    record NoMatch() implements Membership {}

    /** There was no value to hold, and this is what stopped there being one. */
    record Incomplete(Incompleteness.Code code) implements Membership {}

    Membership MATCH = new Match();

    Membership NO_MATCH = new NoMatch();

    static Membership of(boolean holds) {
        return holds ? MATCH : NO_MATCH;
    }

    /**
     * What an observation that did not arrive says, whichever class is asking.
     *
     * <p>Null where there is a value to look at, so a classifier can go on to its own question. Here
     * rather than at each classifier because it is one fact about the observation and not a
     * judgement any class makes — and by the same reading it is not this layer's to state either, so
     * which cases are a reason instead of a value is {@link ObservedValue#unread()}'s to say.
     *
     * <p><b>Of a value, and refused of nothing.</b> The absence a walk answers with is not an
     * observation at all, so there is no observation's word for it and this does not reach for the
     * nearest one. A caller that may arrive with nothing says what nothing means to its own
     * question, where that is known: for a term reading a number it is that the walk had no value,
     * and for a classifier it is that no class holds what is not there.
     */
    static Incomplete unread(ObservedValue value) {
        if (value == null) {
            throw new IllegalArgumentException(
                    "no value arrived, which is not something an observation of one says");
        }
        Incompleteness.Code why = value.unread();
        return why == null ? null : new Incomplete(why);
    }
}
