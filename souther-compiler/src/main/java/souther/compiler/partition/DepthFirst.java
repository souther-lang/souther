package souther.compiler.partition;

import java.util.function.Function;
import java.util.function.Predicate;

/**
 * A search walked depth first: from a state to the states one choice past it, in turn, until a
 * state is a whole way or has nothing past it — and what the figure of such a walk counts.
 *
 * <p><b>Every end the walk reaches is one unit of {@link Tries}</b>: a whole way, and a state with
 * nothing past it, which is a dead end. There is no end that spends nothing. Counted at the whole
 * ways alone, a walk whose later choices all fall away goes through every way of the earlier ones
 * and spends nothing on any of them: work the figure was to bound and never sees, as many times
 * over as the earlier choices multiply. A walk where nothing falls away has no dead end and spends
 * one unit a whole way, which is what such a figure counted before ends of the other kind did.
 *
 * <p>What this bounds is the walking. A state is entered only while a unit is left, and every
 * state entered is on the way to an end, so the states entered are at most as many as the ends
 * the figure allows times how deep the search goes. Past the last unit no state is entered and
 * nothing is walked from one. What is still done is to look whether a state is left to enter,
 * which is what tells a walk cut short from one that ran out: where the states past one are
 * worked out as they are asked for, that looks at most at the next of them, and asks the search
 * to work it out, so a search whose states past one are filtered may look at several to find it.
 * What it costs to work out the states past one, and what is done at a whole way, are the
 * search's own and bounded where they are done.
 *
 * <p>What each end means is the search's as well. A dead end met for a contradiction, for a value
 * nothing works out, or for a reading that stopped are three things to a reader; the walk counts
 * each as an end and nothing more, and a search that has to tell them apart says so where it finds
 * nothing past a state.
 */
final class DepthFirst {

    private DepthFirst() {
    }

    /** How far a walk went. */
    enum Walked {
        /** Every end was reached, and the search went on past each whole way. */
        EVERY_END_REACHED,
        /** The search took a whole way and asked for nothing after it. */
        TAKEN,
        /** A state was to be entered and no unit was left: something was left unwalked. */
        CUT_SHORT
    }

    /**
     * The search walked from {@code from}, held to {@code tries}.
     *
     * @param past the states one choice past a state, in the order they are walked — or null
     *             where it is a whole way. None is a dead end. Worked out as they are walked, so
     *             that a walk cut short works out no more than the next of them, to know one was
     *             left
     * @param goOn what is done with a whole way: whether to go on past it
     */
    static <S> Walked walk(S from, Tries tries, Function<S, Iterable<? extends S>> past,
                           Predicate<S> goOn) {
        if (!tries.left()) {
            return Walked.CUT_SHORT;
        }
        Iterable<? extends S> next = past.apply(from);
        if (next == null) {
            tries.spend();
            return goOn.test(from) ? Walked.EVERY_END_REACHED : Walked.TAKEN;
        }
        boolean any = false;
        for (S each : next) {
            any = true;
            Walked walked = walk(each, tries, past, goOn);
            if (walked != Walked.EVERY_END_REACHED) {
                return walked;
            }
        }
        if (!any) {
            tries.spend();
        }
        return Walked.EVERY_END_REACHED;
    }
}
