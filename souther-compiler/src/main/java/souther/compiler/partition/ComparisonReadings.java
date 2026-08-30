package souther.compiler.partition;

import souther.compiler.types.BinOp;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.inputs.InputReads;

import java.util.ArrayList;
import java.util.List;

/**
 * One reading of a body's comparisons: where each stands, what its names point at, what a row had
 * already satisfied to get there, whether a line may be drawn on it, and what it came to where one
 * may.
 *
 * <p><b>Each comparison is read once, here, and what it came to travels with it.</b> A reader that
 * reports why a comparison bears no line reads the answer off the standing and never reads the
 * arithmetic again: read again downstream, the second reading answers about the form when the
 * question was about where the comparison stands, and a form read to the end is described as one
 * nobody could read.
 *
 * <p><b>One walk, because there is one thing being walked.</b> Three facts about a comparison are
 * settled by where it stands in the body, and each was being worked out by a walk of its own: which
 * names are in force, whether what is computed there is read on the way to an answer, and what the
 * evaluation before it established. Two walks threading the same {@code let} rule through the same
 * tree are two chances to disagree about it, and a fact one of them learned to carry is one the
 * other still drops.
 *
 * <p><b>What stands when a comparison runs is a fact about the position, not about a condition.</b>
 * It was read off {@link Condition}, which is a reading of a subtree and so needs a root — and the
 * root anything ever gave it was a fork's condition. So {@code A && B} established nothing for
 * {@code B} while {@code if A then B else false} did, one model spelled two ways with two answers
 * about where a row for a border on {@code B} is looked for; a name standing for {@code A}
 * established nothing either, because a subtree read on its own has no reading of the names above
 * it. A walk of the body has no root to be given and reaches every position, so what a condition is
 * asked is what it can answer: what a subtree coming out one way establishes
 * ({@link ReachingCuts#stating}), and never where the comparisons are.
 *
 * <p>The two operators are where a walk of the body is not a walk of what runs. {@code &&} and
 * {@code ||} settle as soon as they can, so the right operand runs under what the left one coming
 * out its way established — which is the whole of what makes this per comparison rather than per
 * fork. Everything else evaluates its parts under what stood at it.
 */
final class ComparisonReadings {

    /**
     * One comparison of the body, read where it is written.
     *
     * <p>The reading travels with the comparison because it is not the same at every one of them: a
     * comparison inside an expanded helper is about the argument the call handed it, and read
     * against the names outside the binding it is about nothing at all.
     *
     * @param assumed every condition on the way here, each with what became of it. Empty says
     *                nothing stood on the way, which a comparison at the top of a body is; one this
     *                reading has no arithmetic for is on the list as a decline, so the two are not
     *                one answer
     */
    record Reading(Core.Binary comparison, InputReads reads, List<OnTheWay> assumed,
                   BoundaryPolicy.Standing standing) {}

    private final List<Reading> readings;

    private ComparisonReadings(List<Reading> readings) {
        this.readings = List.copyOf(readings);
    }

    /** Every comparison of {@code body}, in the order the source wrote them. */
    List<Reading> all() {
        return readings;
    }

    /** What each comparison stands under, filed under the site a run through it is recorded at. */
    ReachingCuts reaching(CoverageSites.Plan plan) {
        ReachingCuts.Collected cuts = new ReachingCuts.Collected();
        for (Reading each : readings) {
            plan.comparisonAt(each.comparison())
                    .ifPresent(site -> cuts.reached(site, each.assumed()));
        }
        return cuts.made();
    }

    /**
     * What is the same at every comparison of one body: whose body it is, what the plan numbered,
     * the module's names, what the input's rules leave each quantity, and what the paths leave
     * arriving at each comparison.
     */
    private record Body(String behavior, CoverageSites.Plan plan, Symbols symbols,
                        souther.compiler.inputs.Quantities quantities,
                        souther.compiler.check.PathReachability.Answers arrives) {}

    /**
     * One reading of {@code body}, which is {@code behavior}'s.
     *
     * <p>{@code arrives} is what the walk of the whole body found reaching each comparison, which is
     * one of the two domains a line is held against — the declarations leave the other. It is handed
     * in here because this is where a comparison is read, and a reading of it is made once.
     */
    static ComparisonReadings of(String behavior, Core body, CoverageSites.Plan plan,
                                 InputReads reads, Symbols symbols,
                                 souther.compiler.inputs.Quantities quantities,
                                 souther.compiler.check.PathReachability.Answers arrives) {
        List<Reading> readings = new ArrayList<>();
        walk(body, new Body(behavior, plan, symbols, quantities, arrives), reads, LiveFlow.of(body),
                List.of(), true, readings);
        return new ComparisonReadings(readings);
    }

    /**
     * @param assumed what evaluating everything before this position established
     * @param live    whether what is computed here is read on the way to what the behavior answers
     *                with. Carried down because everything inside a value nothing reads is read by
     *                nothing either
     */
    private static void walk(Core e, Body in, InputReads reads, LiveFlow flow,
                             List<OnTheWay> assumed, boolean live, List<Reading> out) {
        CoverageSites.Plan plan = in.plan();
        Symbols symbols = in.symbols();
        if (e instanceof Core.Binary comparison && plan.comparisons().at(comparison).isPresent()) {
            // Read only where the policy admits it, and under the names in force here, which is
            // the one environment the comparison is about. `answer` is null: a body has nothing
            // that is the answer.
            //
            // And under what arrives at it, which is where a body's comparison differs from a
            // clause's: it stands somewhere, and what the conditions on the way leave is the other
            // domain its line is held against.
            BoundaryPolicy.Standing standing = BoundaryPolicy.refuses(comparison, plan, live)
                    .<BoundaryPolicy.Standing>map(BoundaryPolicy.Standing.Refused::new)
                    .orElseGet(() -> new BoundaryPolicy.Standing.Admitted(
                            ComparisonAssessment.of(in.behavior(), comparison, reads, symbols,
                                    in.quantities(), null, false,
                                    plan.comparisonAt(comparison)
                                            .map(in.arrives()::arrivalAt)
                                            .orElseGet(souther.compiler.reach.ComparisonArrival
                                                    .NoProjection::new))));
            out.add(new Reading(comparison, reads, assumed, standing));
        }
        switch (e) {
            // The right operand runs only where the left came out the way that leaves the answer
            // unsettled, so what it stands under is what that says. Asked of the operand and not of
            // any fork above it: there need not be one, and where there is, this is what the fork
            // would have been reading anyway.
            case Core.Binary both when both.op() == BinOp.AND -> {
                walk(both.left(), in, reads, flow, assumed, live, out);
                walk(both.right(), in, reads, flow,
                        taking(both.left(), true, reads, assumed, symbols), live, out);
            }
            case Core.Binary either when either.op() == BinOp.OR -> {
                walk(either.left(), in, reads, flow, assumed, live, out);
                walk(either.right(), in, reads, flow,
                        taking(either.left(), false, reads, assumed, symbols), live, out);
            }
            // The condition under what stood above the fork, and each arm under what that arm proves
            // of it. A comparison inside a condition is not below the fork: it runs to decide it.
            case Core.If iff -> {
                walk(iff.cond(), in, reads, flow, assumed, live, out);
                walk(iff.then(), in, reads, flow,
                        taking(iff.cond(), true, reads, assumed, symbols), live, out);
                walk(iff.els(), in, reads, flow,
                        taking(iff.cond(), false, reads, assumed, symbols), live, out);
            }
            // What a `let` computes is read on the way to the answer only where the name is read;
            // everywhere else a value stands in a body it is consumed by what it stands in. And its
            // body is where the name stands for what was bound to it.
            case Core.LetIn let -> {
                walk(let.value(), in, reads, flow, assumed, live && flow.reads(let), out);
                walk(let.body(), in, reads.and(let.binder(), let.value()), flow, assumed, live,
                        out);
            }
            // And each arm under what the arm says the value it matched turned out to be. A name
            // the arm binds is the scrutinee's position narrowed to that case, so a comparison
            // written inside an arm draws its line on a position the reading of the input has —
            // read without it, every rule an author writes inside a `match` was about nothing.
            //
            // The same narrowing is what a row has to be for the arm to be reached at all, so it
            // goes onto the account beside the conditions a guard states. Walked without it, a line
            // inside an arm was owed a row by a walk that had been told nothing stood on the way to
            // it, and the row composed for it was written in whichever arm the values fell in.
            case Core.Match match -> {
                walk(match.scrutinee(), in, reads, flow, assumed, live, out);
                for (Core.Case arm : match.cases()) {
                    walk(arm.body(), in, reads.insideArm(match, arm, symbols), flow,
                            entering(match, arm, reads, assumed, symbols), live, out);
                }
            }
            default -> Core.forEachChild(e, child ->
                    walk(child, in, reads, flow, assumed, live, out));
        }
    }

    /**
     * What stands past {@code node} coming out {@code holding}: what stood before it, and what that
     * says.
     *
     * <p>Asked of {@link ReachingCuts#stating}, which is the same rule that says what reaching an
     * arm of a fork establishes. Both are "this subtree came out this way, so what follows", and
     * written apart they would agree by having been derived alike — until one of them learned to
     * read a shape of condition the other did not.
     */
    private static List<OnTheWay> taking(Core node, boolean holding, InputReads reads,
                                         List<OnTheWay> assumed, Symbols symbols) {
        List<OnTheWay> out = new ArrayList<>(assumed);
        out.addAll(ReachingCuts.stating(Condition.of(node, reads), holding, symbols));
        return List.copyOf(out);
    }

    /** The same, for what standing inside one arm of a fork establishes ({@link
     *  ReachingCuts#entering}). */
    private static List<OnTheWay> entering(Core.Match match, Core.Case arm, InputReads reads,
                                           List<OnTheWay> assumed, Symbols symbols) {
        List<OnTheWay> out = new ArrayList<>(assumed);
        out.add(ReachingCuts.entering(match, arm, reads, symbols));
        return List.copyOf(out);
    }
}
