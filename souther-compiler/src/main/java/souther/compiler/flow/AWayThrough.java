package souther.compiler.flow;

import souther.compiler.meaning.WhyNotTaken;

import java.util.LinkedHashSet;
import java.util.List;

/**
 * Whether the rules leave some input on which what a fork's condition states comes out the way an
 * arm needs.
 *
 * <p>Two answers and not three, because only one of them is a proof. The rules leave a value
 * behind a way, or a part of what the condition states was not asked of them at all, and in both
 * cases the way is not ruled out — which is not the same as a run being shown to take it. What the
 * rules leave is an upper bound: a set disjoint from it is disjoint from what arrives, and a set it
 * meets need not meet what arrives. So a way not ruled out is entered and is never a witness that
 * something arrives there.
 */
public sealed interface AWayThrough {

    /** The rules leave no input on which the condition comes out this way: no run enters. */
    record RuledOut() implements AWayThrough {}

    /**
     * Not ruled out, and every part of what the condition states that was not asked of the rules,
     * each once. Empty where every part was asked and the rules left a value behind each.
     */
    record NotRuledOut(List<WhyNotTaken> notAsked) implements AWayThrough {

        public NotRuledOut {
            notAsked = List.copyOf(new LinkedHashSet<>(notAsked));
        }
    }
}
