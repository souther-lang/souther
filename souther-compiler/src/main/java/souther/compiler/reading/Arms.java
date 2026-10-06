package souther.compiler.reading;

import souther.compiler.core.Core;
import souther.compiler.coverage.ArmProbe;
import souther.compiler.coverage.ControlClaim;
import souther.compiler.coverage.ControlPlace;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.coverage.SourceOutcome;
import souther.compiler.flow.ValueArrivals;
import souther.compiler.flow.Ways;
import souther.compiler.types.SourceConstruct;

import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.SequencedMap;

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

    private final Map<ArmProbe, PathAccess> byArm =
            new LinkedHashMap<>();

    /** The fork each arm was met under, as the node the walk met it at. Two splices of one helper
     *  are two nodes, which is what makes them two forks. */
    private final Map<ArmProbe, Core> forkOf = new LinkedHashMap<>();

    /** The body each arm was met in: the behavior's own, or a method it calls. */
    private final Map<ArmProbe, Core> bodyOf = new LinkedHashMap<>();

    Arms(CoverageSites.Plan plan) {
        this.plan = plan;
    }

    /**
     * How arm {@code part} of {@code fork} is reached, where the plan numbered that arm.
     *
     * <p>An arm no run could be recorded at is not one anything reports, so nothing is kept for it
     * — and it is the same answer that decides both: what a run at the arm would be seen doing is
     * what the reading here is handed on with, and where there is none there is nothing to hold a
     * row to.
     *
     * @param body the body {@code fork} is written in, which is what a name in its condition is
     *             read against
     */
    void at(Core fork, int part, Reach reach, Core body) {
        ControlPlace.Arm[] arms = plan.armsOf(fork);
        if (arms == null || part < 0 || part >= arms.length || arms[part] == null) {
            return;
        }
        ControlClaim.of(arms[part]).ifPresent(arrivesAt -> {
            byArm.put(arms[part].probe().get(), reach.told(arrivesAt));
            forkOf.put(arms[part].probe().get(), fork);
            bodyOf.put(arms[part].probe().get(), body);
        });
    }

    /**
     * For each arm of {@code behavior} that leaves a {@code guard} because its condition did not
     * hold, the arm of the same guard that is the rest of the block and each way its condition lets
     * a run go on there.
     *
     * <p>Paired by the node the walk met them at — compared as that object, since two splices of
     * one helper are two guards and a run past one has not passed the other.
     *
     * <p>The ways are read off the body the guard is written in by the walk that reads it, named
     * for what a run would be seen doing ({@link WhatARunIsSeenDoing}), and asked of each guard's
     * condition. Over the whole body and not the condition alone, because what a name in the
     * condition stands for is what the body bound it to above. Not walked where the body has no
     * guard, and once for each body that has one.
     */
    SequencedMap<ArmProbe, TheRestOfTheBlock> restOfTheBlock(String behavior) {
        Map<Core, ArmProbe> heldAt = new IdentityHashMap<>();
        List<CoverageSites.ArmSite> sites = plan.arms(behavior);
        for (CoverageSites.ArmSite arm : sites) {
            if (arm.construct() == SourceConstruct.GUARD
                    && arm.outcome() instanceof SourceOutcome.Held) {
                heldAt.put(forkOf.get(arm.index()), arm.index());
            }
        }
        SequencedMap<ArmProbe, TheRestOfTheBlock> out = new LinkedHashMap<>();
        Map<Core, ValueArrivals<List<ControlClaim>>> seenIn = new IdentityHashMap<>();
        for (CoverageSites.ArmSite arm : sites) {
            Core fork = forkOf.get(arm.index());
            ArmProbe goesOn = heldAt.get(fork);
            if (arm.construct() != SourceConstruct.GUARD
                    || !(arm.outcome() instanceof SourceOutcome.Failed) || goesOn == null
                    || !(fork instanceof Core.If guard)) {
                continue;
            }
            ValueArrivals<List<ControlClaim>> seen = seenIn.computeIfAbsent(
                    bodyOf.get(arm.index()), body -> {
                        WhatARunIsSeenDoing naming = new WhatARunIsSeenDoing(plan);
                        return ValueArrivals.ofBody(body, naming, naming.eitherWay());
                    });
            List<List<ControlClaim>> ways =
                    seen.waysTo(guard.cond(), partOf(fork, goesOn) == 0)
                            instanceof Ways.Known<List<ControlClaim>> known
                            ? known.paths() : List.of();
            out.put(arm.index(), new TheRestOfTheBlock(goesOn, ways));
        }
        return Collections.unmodifiableSequencedMap(out);
    }

    /** Which arm of {@code fork} the plan numbered {@code probe}. */
    private int partOf(Core fork, ArmProbe probe) {
        ControlPlace.Arm[] arms = plan.armsOf(fork);
        for (int part = 0; part < arms.length; part++) {
            if (arms[part] != null && arms[part].probe().equals(Optional.of(probe))) {
                return part;
            }
        }
        throw new IllegalStateException(
                "arm " + probe + " was recorded under a fork the plan numbers no such arm of");
    }

    /**
     * One answer per arm of {@code behavior}, in the order the plan numbered them.
     *
     * <p>The plan's arms are the whole of it, and that the walk reached every one of them is
     * checked here rather than made true by filling in. An arm this reading never got to is not a
     * kind of answer — it is this reading falling short of what it says it does — and written as
     * one it would be a value a reader has to act on, indistinguishable from the arms whose way in
     * really is beyond what the path language states. The check would then hold of a walk that
     * stopped early, which is the whole of what it is for.
     */
    java.util.SequencedMap<ArmProbe, PathAccess> found(String behavior) {
        // Walked over the plan's own arms, so the order these come back in is the order the plan
        // holds the behavior's arms in. Which is what whoever asks for a row at each of them takes
        // as the order to ask in, and it is only that because this walk is where it comes from.
        java.util.SequencedMap<ArmProbe, PathAccess> out =
                new LinkedHashMap<>();
        for (CoverageSites.ArmSite arm : plan.arms(behavior)) {
            PathAccess access = byArm.get(arm.index());
            if (access == null) {
                throw new IllegalStateException("the reading of `" + behavior + "` did not reach"
                        + " arm " + arm.index() + " of " + arm.obligation().origin()
                        + "; every arm the plan numbered is one this walk goes to");
            }
            out.put(arm.index(), access);
        }
        return java.util.Collections.unmodifiableSequencedMap(out);
    }
}
