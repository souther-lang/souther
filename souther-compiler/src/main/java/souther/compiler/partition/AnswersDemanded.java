package souther.compiler.partition;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * What a way through a body asks of the answers a row stands its dependencies in with.
 *
 * <p>Both halves, for the reason {@link WayToTheBorder} keeps both of its: what was stated is what a
 * search composes an answer against, and what could not be stated is a condition a value standing a
 * dependency in was not composed against. Split apart, "the way asks nothing of any answer" and
 * "everything it asks was stated" come out as the same empty answer, and only the second is a way a
 * composed row reaches.
 *
 * <p><b>Neither half is a gate.</b> Whether a value can be composed for what was stated is settled
 * by composing it, two stages further on, and nothing here knows the answer. What this says is what
 * the reading of the way came to, which travels as an account beside whatever the composition then
 * came to rather than deciding in advance that there is nothing to try.
 *
 * @param stated   the demands, in the order the walk met the conditions they came from
 * @param declined the conditions about an answer that this has no way of stating, each saying where
 *                 a report about it asks for its place and what stopped it
 */
public record AnswersDemanded(List<AnswerDemand> stated,
                              List<DemandGap.Unstated> declined) {

    /** A way that asks nothing of any answer, which is what a body deciding on its input alone
     *  states. */
    public static final AnswersDemanded NOTHING = new AnswersDemanded(List.of(), List.of());

    public AnswersDemanded {
        stated = List.copyOf(stated);
        declined = List.copyOf(declined);
    }

    /**
     * The conditions this reading answered for, whether it stated them or wrote down that it could
     * not.
     *
     * <p>What the other projection of the same conditions is reconciled against
     * ({@link CompositionAccount}). A condition in here is one the input projection has no words
     * for and needs none: it is about an answer, and the account of what a row was composed without
     * takes what became of it from this side.
     */
    public Set<ConditionReportAnchor> takenUp() {
        if (stated.isEmpty() && declined.isEmpty()) {
            return Set.of();
        }
        Set<ConditionReportAnchor> out = new LinkedHashSet<>();
        stated.forEach(each -> out.add(each.anchor()));
        declined.forEach(each -> out.add(each.anchor()));
        return out;
    }

    /** The demands on each answer, in the order the answers were first asked about. */
    public Map<InjectedAnswer, List<AnswerDemand>> byAnswer() {
        Map<InjectedAnswer, List<AnswerDemand>> out = new LinkedHashMap<>();
        for (AnswerDemand each : stated) {
            out.computeIfAbsent(each.of(), _ -> new ArrayList<>()).add(each);
        }
        return out;
    }
}
