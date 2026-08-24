package souther.compiler.interaction;

import souther.compiler.core.Core;
import souther.compiler.coverage.ControlPointId;
import souther.compiler.coverage.CoverageSites;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * How each arm of a body is reached, one answer per arm the plan numbered.
 *
 * <p>Total over the arms of the behavior, which is what makes it worth asking. A measure that finds
 * an arm no row goes through hands the arm on to whatever composes rows, and an arm the reading had
 * nothing on used to be an arm nobody could say anything about: the absence was read as a fact about
 * the body — that nothing takes it — which is not what an absence says. Every arm the plan numbered
 * is here, and an arm this reading never got to says so in as many words.
 *
 * <p>By the number the plan gave the arm, which is the number the site carries and the number a
 * finding is written against. One identity, not two spellings that agree until one moves.
 *
 * <p>The arms and not the obligations. Two occurrences of one arm put together are one thing to
 * report and two places in the body, and what it takes to reach them is what differs — so an answer
 * held per obligation would be one occurrence's way in standing for another's.
 */
final class Arms {

    private final CoverageSites.Plan plan;

    private final Map<Integer, PathAccess> byArm = new LinkedHashMap<>();

    Arms(CoverageSites.Plan plan) {
        this.plan = plan;
    }

    /** How arm {@code part} of {@code fork} is reached, where the plan numbered that arm. An arm no
     *  run could be recorded at is not one anything reports, so nothing is kept for it. */
    void at(Core fork, int part, Reach reach) {
        ControlPointId.ArmOccurrence[] arms = plan.armsOf(fork);
        if (arms == null || part < 0 || part >= arms.length || arms[part] == null
                || arms[part].probe().isEmpty()) {
            return;
        }
        byArm.put(arms[part].probe().getAsInt(), reach.told());
    }

    /**
     * One answer per arm of {@code behavior}, in the order the plan numbered them.
     *
     * <p>The plan's arms are the whole of it. What the walk recorded is what it reached, and an arm
     * missing from that is not an arm without a way in — it is this reading having fallen short, and
     * it is written as that rather than left out. A caller reading a key that is not there would be
     * deciding what the absence meant, which is the thing this type exists to stop.
     */
    Map<Integer, PathAccess> found(String behavior) {
        Map<Integer, PathAccess> out = new LinkedHashMap<>();
        for (CoverageSites.Site arm : plan.arms(behavior)) {
            out.put(arm.index(), byArm.getOrDefault(arm.index(), new PathAccess.Unsupported(
                    PathAccess.Unsupported.Why.THE_READING_DID_NOT_REACH_IT)));
        }
        return java.util.Collections.unmodifiableMap(out);
    }
}
