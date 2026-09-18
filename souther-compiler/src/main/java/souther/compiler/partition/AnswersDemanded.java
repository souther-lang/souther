package souther.compiler.partition;

import java.util.ArrayList;
import java.util.LinkedHashMap;
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
 * <p><b>And which conditions this side answered for is its own answer.</b> The reading over the
 * input declines every condition about an answer, so an account of what a row was composed without
 * has to know which of those declines this side has something to say about. What joins the two is
 * the condition, which the reading names ({@link ConditionOccurrence}) — a helper expanded twice
 * puts two conditions in a body and a report sends a reader to the one place either is written, so
 * a join on where they are reported would answer for one of them with what became of the other.
 *
 * @param stated   the demands, in the order the walk met the conditions they came from
 * @param declined the conditions about an answer that this has no way of stating, each saying where
 *                 a report about it asks for its place and what stopped it
 * @param takenUp  which conditions of the reading this side answered for, named the way the reading
 *                 names a condition. Held rather than worked out from the two lists above, because
 *                 what those carry is where a report about a condition points, and where is not
 *                 which: one condition an author wrote stands once per call of the helper holding
 *                 it, and every one of them is reported at the one place it is written
 */
public record AnswersDemanded(List<AnswerDemand> stated,
                              List<DemandGap.Unstated> declined,
                              Set<ConditionOccurrence> takenUp) {

    /** A way that asks nothing of any answer, which is what a body deciding on its input alone
     *  states. */
    public static final AnswersDemanded NOTHING =
            new AnswersDemanded(List.of(), List.of(), Set.of());

    public AnswersDemanded {
        stated = List.copyOf(stated);
        declined = List.copyOf(declined);
        takenUp = Set.copyOf(takenUp);
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
