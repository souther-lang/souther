package souther.compiler.check;

import souther.compiler.numeric.EndSide;
import souther.compiler.numeric.Endpoint;
import souther.compiler.types.TypeSymbol;

import java.util.List;

/**
 * Declarations holding an end, and the end a reading has just been asked about turning out to be
 * that one.
 *
 * <p><b>This proves that and nothing further.</b> One of these says the names were worked out
 * against the end whose side and place it carries — it does not say a report should print them.
 * Whether it should is the consumer's own rule, asked after this and with what that consumer knows:
 * a cut asks whether the position's own type already stopped there, and a run asks whether it
 * actually stops at the place this end lowers to. {@link Endpoint#sameAs} says two ends are one
 * end; it does not say a reader wants to hear about it, and reading this as permission to print
 * would put the second answer where the first is.
 *
 * <p><b>The side as well as the place, because the two ends can be the same end.</b> A range
 * holding one value stops there both ways. Matched on the place alone, what was worked out at the
 * low end comes back as an answer about the high one.
 *
 * <p>Only a reading makes one of these, and only by being asked about an end it has. So a caller
 * holding one is a caller whose end was compared, and there is nowhere else to obtain the names.
 */
public final class MatchedEndAttribution {

    private final EndSide side;
    private final Endpoint endpoint;
    private final Held held;

    MatchedEndAttribution(EndSide side, Endpoint endpoint, Held held) {
        this.side = side;
        this.endpoint = endpoint;
        this.held = held;
    }

    /** Which of the two ends the names are about. */
    public EndSide side() {
        return side;
    }

    /** Where that end is, as the reading that worked the names out left it. */
    public Endpoint endpoint() {
        return endpoint;
    }

    /**
     * The declarations, which is where they stop being held against an end.
     *
     * <p>Public because the consumer that finishes the attribution is in another package, and left
     * as the last step rather than as a guard: what keeps a name from being written beside a
     * stranger's end is that nothing downstream accepts a bare list of them. A caller that reads
     * these has nowhere to put them but the point this attribution is about.
     *
     * <p>Asking does the work the names were left to do later, once. A consumer that has decided
     * not to print them should not ask.
     */
    public List<TypeSymbol.AtModule> names() {
        return held.names();
    }

    Held held() {
        return held;
    }
}
