package souther.compiler.reading;

import souther.compiler.types.BinOp;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.flow.Arrival;
import souther.compiler.flow.Paths;
import souther.compiler.flow.ValueArrivals;
import souther.compiler.semantics.Accumulation;

import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
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
 * an operand of an operator, an argument of a call that answers one value, or the elements of a
 * list that a total adds up — written out in the body, or kept by a comparison
 * ({@link KeptElements}).
 */
final class Meetings {

    private final CoverageSites.Plan plan;

    /** The nodes one operator's run is written as, which the walk meets again on its way down and
     *  which are no meeting of their own. Identity and not equality: two operands written the same
     *  are two places. */
    private final Set<Core> absorbed = Collections.newSetFromMap(new IdentityHashMap<>());

    /** What a comparison the walk has passed is made of: the operands it compares. */
    private final Set<Core> compared = Collections.newSetFromMap(new IdentityHashMap<>());

    private final List<Interaction> found = new ArrayList<>();

    private final List<WhyNotJoined> notJoined = new ArrayList<>();

    /** The elements a call adds up that a comparison keeps. */
    private final KeptElements keptElements;

    Meetings(CoverageSites.Plan plan, KeptElements keptElements) {
        this.plan = plan;
        this.keptElements = keptElements;
    }

    /**
     * Whatever meets at {@code node}, under every way in the walk arrived by.
     *
     * <p>A meeting reached several ways is one place in the body and as many groups, and they are
     * written down together because that is when the walk is there.
     *
     * @param body    the body holding {@code node}, which is where a comparison the elements of a
     *                list were written with is found when it is not in the call that consumes them
     * @param reading what the body holding {@code node} was read to arrive at, and by which ways.
     *                The walk's reading, handed in rather than taken again: what a value is settled
     *                by is one question and is asked once
     */
    void at(Core node, CoverageNaming naming, Core body, List<List<Decision>> reaches,
            ValueArrivals<Outcome> reading) {
        // No way in is none stated, which is a position the walk is at whatever it can say of how it
        // was reached: what a meeting there is made of is read all the same, and said where it
        // cannot be offered.
        // A walk meets a comparison before the operands it compares.
        if (Core.withoutStanding(node) instanceof Core.Binary binary && binary.op().compares()) {
            compared.add(Core.withoutStanding(binary.left()));
            compared.add(Core.withoutStanding(binary.right()));
        }
        if (absorbed.contains(node)) {
            return;
        }
        List<Core> meeting = meetingAt(node, absorbed);
        List<Factor> factors = new ArrayList<>();
        if (meeting != null) {
            List<Reached> operands = distinct(meeting.stream()
                    .map(operand -> outcomesOf(operand, reading)).toList());
            WhyNotJoined why = whyNotOffered(operands);
            if (why != null) {
                notJoined.add(why);
                return;
            }
            for (Reached each : operands) {
                // One outcome is no decision: the operand answers the same way however the row is
                // written, so nothing about it can be varied against the other operand.
                if (each.outcomes().size() > 1) {
                    factors.add(new Factor(each.outcomes()));
                }
            }
        } else if (node instanceof Core.Call call) {
            switch (keptElements.of(call, naming, body, compared.contains(call))) {
                case null -> {
                    return;
                }
                // Met once however many ways reach it: it is a place in the body that was not read,
                // and the ways in say nothing more about that.
                case KeptElements.Read.NotJoined(var why) -> {
                    notJoined.add(why);
                    return;
                }
                case KeptElements.Read.Factors found -> factors.addAll(found.each());
            }
        } else {
            return;
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
        // A meeting is of decisions, and an operand is only a place one is used. The same decision
        // used in two operands — a choice named once and added to itself — is one factor: it
        // cannot come out one way in the first and the other in the second, so a combination
        // that says it does is one no row could make.
        List<Factor> apart = new ArrayList<>(new LinkedHashSet<>(factors));
        if (apart.size() > 1) {
            if (plan.mayRepeat(node)) {
                notJoined.add(WhyNotJoined.THE_MEETING_IS_IN_CODE_RUN_AGAIN);
            } else if (reaches.isEmpty()) {
                notJoined.add(WhyNotJoined.THE_WAY_IN_CANNOT_BE_STATED);
            } else {
                for (List<Decision> reach : reaches) {
                    found.add(new Interaction(reach, apart));
                }
            }
        }
    }

    /** What reads the decisions that keep the elements a call counts or adds up. */
    KeptElements keptElements() {
        return keptElements;
    }

    /** The groups, in the order the walk met them. */
    List<Interaction> found() {
        return List.copyOf(found);
    }

    /** The sums of kept elements the walk met and could not join to evaluations, each with the
     *  reason, in the order it met them. They are meetings the measure did not ask about. */
    List<WhyNotJoined> notJoined() {
        return List.copyOf(notJoined);
    }

    /**
     * The ways {@code e} can be settled that a group can be composed against.
     *
     * <p>A projection of the reading and not a second walk. Two ways written down the same are one
     * way: a value settled twice over by the reading getting there twice is settled once, and a
     * factor counting the second would report a value varying where it does not.
     *
     * <p>Each as what a run on it is seen doing ({@link souther.compiler.flow.Provenance#seen}),
     * which is what a group is met by. A way into an arm a run is not seen taking one of is the arm
     * here, which is all a run there shows: offered as itself, a run down another way into the arm
     * would be seen meeting it.
     */
    private static Reached outcomesOf(Core e, ValueArrivals<Outcome> reading) {
        return reachedBy(reading.waysAt(e));
    }

    /**
     * What an operand is settled by, from the ways the reading holds of it.
     *
     * <p>Three things and not two: no way at all, where no run arrives; the ways, which are the
     * outcomes; and ways this reading will not hold apart ({@link Paths.Beyond}), of which nothing
     * is known. The last is no more "none" than it is any number: it is an answer about what this
     * reading enumerates, and reading it as an empty list would take an operand that may be a
     * decision out of the meeting.
     */
    static Reached reachedBy(Paths<Outcome> ways) {
        return ways instanceof Paths.Held<Outcome>(var arrivals) ? outcomesFrom(arrivals)
                : Reached.NOT_ENUMERATED;
    }

    /**
     * The outcomes of an operand, and what is not known of them.
     *
     * @param outcomes     the ways it is settled that a run is seen taking
     * @param unseen       how many ways the reading holds of it that no run is seen taking, so that
     *                     no combination with one can be held to a run. At least that many, and a
     *                     way that is one of them is not one this counts: the reading keeps ways
     *                     that are alike as one, and two arms that nothing tells apart are alike
     * @param unenumerated whether the ways it is settled by are more than this reading holds apart
     */
    record Reached(List<Outcome> outcomes, int unseen, boolean unenumerated) {

        /** Nothing is known of the ways: there are more than are held apart. */
        static final Reached NOT_ENUMERATED = new Reached(List.of(), 0, true);

        Reached {
            outcomes = List.copyOf(outcomes);
        }

        /** Whether every way the operand is settled by is known and seen. */
        boolean known() {
            return unseen == 0 && !unenumerated;
        }

        /**
         * Whether the operand may be settled more than one way, which is a decision.
         *
         * <p>Where a way is not seen, how many ways it stands for is not known: two that nothing
         * tells apart are held as one. So one such way is as much a decision as many, and no count
         * of them is taken for the number there are.
         */
        boolean mayVary() {
            return unenumerated || unseen > 0 || outcomes.size() > 1;
        }
    }

    /**
     * The operands, the same decision used in two of them being one.
     *
     * <p>Told apart only where everything of an operand is known. Two operands of which the same is
     * not known are not shown to be the same decision, and are two: equal readings of what cannot be
     * read say nothing of whether they are one choice named twice.
     */
    static List<Reached> distinct(List<Reached> operands) {
        List<Reached> out = new ArrayList<>();
        for (Reached each : operands) {
            if (!(each.known() && out.contains(each))) {
                out.add(each);
            }
        }
        return out;
    }

    /**
     * Why {@code operands} cannot be offered as a meeting, or null where they can.
     *
     * <p>A meeting is of two decisions at least. An operand some of whose ways are not known may be
     * one, so where another is, or another may be, the combinations cannot be named: said, and not
     * measured over the operands that are known and called whole.
     */
    static WhyNotJoined whyNotOffered(List<Reached> operands) {
        if (operands.stream().filter(Reached::mayVary).count() < 2) {
            return null;
        }
        if (operands.stream().anyMatch(Reached::unenumerated)) {
            return WhyNotJoined.AN_OPERAND_HAS_MORE_WAYS_THAN_ARE_READ;
        }
        return operands.stream().anyMatch(each -> each.unseen() > 0)
                ? WhyNotJoined.AN_OUTCOME_NO_RUN_IS_SEEN_TAKING : null;
    }

    /**
     * The outcomes {@code arrivals} reach, as what a run is seen doing: two ways a run is not seen
     * to tell apart are one outcome, which a row settles by either.
     *
     * <p>Whether there is an outcome does not turn on whether the ways to it could be written down.
     * What identifies it is what a run is seen doing there, which is the arm a run is seen at or the
     * way itself where that was written whole. Where a way has neither, the outcome is the operand's
     * all the same and is said ({@code unseen}) and not dropped.
     *
     * <p>An outcome is told the ways that reach it only where every one of them was written down
     * whole. One the naming could not write is a part of the region the others do not state, and the
     * union of the rest would be narrower than the outcome. Such an outcome is still offered, with
     * the region left unsaid.
     */
    static Reached outcomesFrom(List<Arrival<Outcome>> arrivals) {
        Map<Outcome, List<Arrival<Outcome>>> reaching = new LinkedHashMap<>();
        for (Arrival<Outcome> each : arrivals) {
            reaching.computeIfAbsent(each.provenance().seen(), _ -> new ArrayList<>()).add(each);
        }
        List<Outcome> out = new ArrayList<>();
        int unseen = 0;
        for (Map.Entry<Outcome, List<Arrival<Outcome>>> one : reaching.entrySet()) {
            List<Arrival<Outcome>> reached = one.getValue();
            if (reached.stream().noneMatch(each -> each.isComplete()
                    || !each.provenance().isSeenWhole())) {
                unseen += reached.size();
                continue;
            }
            out.add(reached.stream().allMatch(Arrival::isComplete)
                    ? one.getKey().comingOutBy(reached.stream()
                            .map(each -> each.path().holds().stream()
                                    .map(Decision::constrains).toList())
                            .toList())
                    : one.getKey());
        }
        return new Reached(out, unseen, false);
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
            case Core.Call call -> {
                List<Core> written = numbersWrittenOutIn(call);
                yield written != null ? written : call.args().size() > 1 ? call.args() : null;
            }
            case Core.PreservedCall call -> call.args().size() > 1 ? call.args() : null;
            case Core.Apply apply -> apply.args().size() > 1 ? apply.args() : null;
            default -> null;
        };
    }

    /**
     * The elements of the list written out in {@code call}, where the call adds or multiplies the
     * elements of its only argument; null otherwise.
     *
     * <p>Which operations walk a container, and how, is the library's to say. Such a call consumes
     * the elements into one value as an operator does its operands, so each element is a value
     * making it. A list that is only built is no meeting, and neither is an operation that joins
     * what it is given rather than combining it into a number.
     */
    private static List<Core> numbersWrittenOutIn(Core.Call call) {
        return combinesItsElements(call)
                && Core.withoutStanding(call.args().getFirst()) instanceof Core.ListLit list
                ? list.elements() : null;
    }

    /** Whether {@code call} adds or multiplies the elements of its only argument. */
    static boolean combinesItsElements(Core.Call call) {
        return accumulationOf(call) != null;
    }

    /** How {@code call} adds or multiplies the elements of its only argument, or null where it
     *  does not. */
    static Accumulation accumulationOf(Core.Call call) {
        if (!(call.fn() instanceof Core.Reached.OfKernel kernel) || call.args().size() != 1) {
            return null;
        }
        Accumulation walk = DefaultBoundOperationFacts.get().accumulation(kernel.name().denotes());
        return walk != null && walk.combine() != Accumulation.Combine.APPEND ? walk : null;
    }

    /** Whether {@code call} answers how many elements its only argument holds. */
    static boolean countsItsElements(Core.Call call) {
        return call.fn() instanceof Core.Reached.OfKernel kernel && call.args().size() == 1
                && DefaultBoundOperationFacts.get().answersHowManyItHolds(kernel.name().denotes());
    }

    /**
     * Whether {@code call} answers a number that depends on which elements its only argument holds:
     * what they add up to, or how many there are.
     *
     * <p>Of a list written out whose elements are all there, the second is no decision of any
     * element — two is two however the choices come out — and only the first is a meeting. Of a
     * list some comparison keeps, both are: which elements are there is what the keeping decides.
     */
    static boolean consumesItsElements(Core.Call call) {
        return combinesItsElements(call) || countsItsElements(call);
    }

    /** The values one run of {@code op} is over, and the nodes the run is written as. */
    private static void run(Core e, BinOp op, List<Core> operands, List<Core> inner) {
        if (Core.withoutStanding(e) instanceof Core.Binary binary && binary.op() == op) {
            inner.add(binary);
            run(binary.left(), op, operands, inner);
            run(binary.right(), op, operands, inner);
        } else if (e != null) {
            operands.add(e);
        }
    }
}
