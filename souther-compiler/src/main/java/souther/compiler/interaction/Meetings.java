package souther.compiler.interaction;

import souther.compiler.types.BinOp;
import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.flow.Arrival;
import souther.compiler.flow.ValueArrivals;

import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Set;

/**
 * Where the decisions of a body determine one value together, collected as the walk meets them.
 *
 * <p>What this owns is the finding and not the getting there. Which places a walk visits and what
 * holds on the way to each is {@link CoverageRead}'s, and is shared with whatever else is read off
 * the same walk; what a meeting is, which nodes one operator's run takes in, and which of them have
 * already been taken in are this reading's own and are here. Kept in the walk instead, the state
 * one of these readings needs would be state the other is held to.
 *
 * <p>A node with several children is not a meeting. Under
 * {@code Order { price = if A then 100 else 200, message = if B then "x" else "y" }} the two
 * decisions arrive at a constructor and interact in nothing, because no observation is a function
 * of both. A group forms only where two values each settled by a decision are consumed into one:
 * an operand of an operator, or an argument of a call that answers one value.
 */
final class Meetings {

    private final CoverageSites.Plan plan;

    /** What the body was read to arrive at, and by which ways. The walk's reading, handed in rather
     *  than taken again: what a value is settled by is one question and is asked once. */
    private final ValueArrivals<Outcome> reading;

    /** The nodes one operator's run is written as, which the walk meets again on its way down and
     *  which are no meeting of their own. Identity and not equality: two operands written the same
     *  are two places. */
    private final Set<Core> absorbed = Collections.newSetFromMap(new IdentityHashMap<>());

    private final List<Interaction> found = new ArrayList<>();

    Meetings(CoverageSites.Plan plan, ValueArrivals<Outcome> reading) {
        this.plan = plan;
        this.reading = reading;
    }

    /**
     * Whatever meets at {@code node}, under every way in the walk arrived by.
     *
     * <p>A meeting reached several ways is one place in the body and as many groups, and they are
     * written down together because that is when the walk is there.
     */
    void at(Core node, List<List<Decision>> reaches) {
        List<Core> meeting = absorbed.contains(node) ? null : meetingAt(node, absorbed);
        if (meeting == null) {
            return;
        }
        List<Factor> factors = new ArrayList<>();
        for (Core operand : meeting) {
            List<Outcome> outcomes = outcomesOf(operand);
            // One outcome is no decision: the operand answers the same way however the row is
            // written, so nothing about it can be varied against the other operand.
            if (outcomes.size() > 1) {
                factors.add(new Factor(outcomes));
            }
        }
        // A group says that these decisions were settled these ways and met here, which is a
        // statement about one passing. What can be established about a run is what its recording
        // holds, and that is which places it passed rather than how many times it passed each —
        // so where a run may come back to this meeting, the two factors coming out the named
        // ways is not something any reading of such a recording can tell from their coming out
        // those ways on different times round. The group would be one nothing could ever show a
        // row to sit in, so it is not offered.
        //
        // Asked at the meeting and nowhere else, which is enough because a place a run may come
        // back to has everything inside it in the same position: a meeting this is false of
        // names a way in and factors that are all false of it too.
        //
        // What varies here is read once and the ways in are as many as they are: an operand is
        // settled the same ways whichever way round the forks above a row went, so the factors
        // are no part of what a way in decides and are not read again per way.
        if (factors.size() > 1 && !plan.mayRepeat(node)) {
            for (List<Decision> reach : reaches) {
                found.add(new Interaction(reach, factors));
            }
        }
    }

    /** The groups, in the order the walk met them. */
    List<Interaction> found() {
        return List.copyOf(found);
    }

    /**
     * The ways {@code e} can be settled that a group can be composed against.
     *
     * <p>A projection of the reading and not a second walk. Two ways written down the same are one
     * way: a value settled twice over by the reading getting there twice is settled once, and a
     * factor counting the second would report a value varying where it does not.
     *
     * <p>A way the naming could not write down whole is not one of these. What a factor offers is a
     * combination a row is steered into, and the conditions of such a way do not say what would
     * steer one there — so it is left out, and where that leaves none the value is answered as
     * varying in no way this can compose against rather than as varying in one nobody can reach.
     */
    private List<Outcome> outcomesOf(Core e) {
        List<Outcome> out = new ArrayList<>();
        for (Arrival<Outcome> each : reading.waysAt(e).orNone()) {
            if (each.isComplete() && !out.contains(each.path())) {
                out.add(each.path());
            }
        }
        return out;
    }

    /**
     * The values consumed into one here, or null where this node consumes none.
     *
     * <p>A run of one operator is one meeting. {@code a + b + c} is written as one operator applied
     * twice and is three values making one, so reading it as two meetings would ask for the product
     * of the left two against the third and then again for the product of the first two — the
     * second being a projection of the first, and every row of it a row the first already wanted.
     * The nodes taken into the run are recorded so the walk does not meet them again.
     */
    private static List<Core> meetingAt(Core node, Set<Core> absorbed) {
        return switch (node) {
            case Core.Binary binary when binary.op().stopsWhenItsAnswerIsSettled() -> null;
            case Core.Binary binary -> {
                List<Core> operands = new ArrayList<>();
                List<Core> inner = new ArrayList<>();
                run(binary.left(), binary.op(), operands, inner);
                run(binary.right(), binary.op(), operands, inner);
                if (operands.size() < 2) {
                    yield null;
                }
                absorbed.addAll(inner);
                yield operands;
            }
            case Core.Call call -> call.args().size() > 1 ? call.args() : null;
            case Core.PreservedCall call -> call.args().size() > 1 ? call.args() : null;
            case Core.Apply apply -> apply.args().size() > 1 ? apply.args() : null;
            default -> null;
        };
    }

    /** The values one run of {@code op} is over, and the nodes the run is written as. */
    private static void run(Core e, BinOp op, List<Core> operands, List<Core> inner) {
        if (e instanceof Core.Binary binary && binary.op() == op) {
            inner.add(binary);
            run(binary.left(), op, operands, inner);
            run(binary.right(), op, operands, inner);
        } else if (e != null) {
            operands.add(e);
        }
    }
}
