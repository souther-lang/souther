package souther.compiler.partition;

import souther.compiler.ast.Hir;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.inputs.InputReads;

import java.util.ArrayList;
import java.util.List;

/**
 * One reading of a body's comparisons: where each stands, what its names point at, what a row had
 * already satisfied to get there, and whether a line is drawn on it.
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

    /** The comparisons a line is drawn on, in the order the source wrote them. */
    List<Reading> drawn() {
        return readings.stream()
                .filter(each -> each.standing() instanceof BoundaryPolicy.Standing.DrawsALine)
                .toList();
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

    /** One reading of {@code body}. */
    static ComparisonReadings of(Core body, CoverageSites.Plan plan, InputReads reads,
                                 Symbols symbols) {
        List<Reading> readings = new ArrayList<>();
        walk(body, plan, reads, symbols, LiveFlow.of(body), List.of(), true, true, readings);
        return new ComparisonReadings(readings);
    }

    /**
     * @param assumed what evaluating everything before this position established
     * @param live    whether what is computed here is read on the way to what the behavior answers
     *                with. Carried down because everything inside a value nothing reads is read by
     *                nothing either
     * @param each    whether every pass of this position in one run is one occurrence of a position
     *                of the input. Carried down for the same reason: a closure applied once per
     *                element stands inside whatever applies the closure above it, and one that
     *                nothing says the applications of settles it for everything under it
     */
    private static void walk(Core e, CoverageSites.Plan plan, InputReads reads, Symbols symbols,
                             LiveFlow flow, List<OnTheWay> assumed, boolean live,
                             boolean each, List<Reading> out) {
        if (e instanceof Core.Binary comparison && plan.comparisons().at(comparison).isPresent()) {
            out.add(new Reading(comparison, reads, assumed,
                    BoundaryPolicy.standingOf(comparison, plan, live, each)));
        }
        switch (e) {
            // The right operand runs only where the left came out the way that leaves the answer
            // unsettled, so what it stands under is what that says. Asked of the operand and not of
            // any fork above it: there need not be one, and where there is, this is what the fork
            // would have been reading anyway.
            case Core.Binary both when both.op() == Hir.BinOp.AND -> {
                walk(both.left(), plan, reads, symbols, flow, assumed, live, each, out);
                walk(both.right(), plan, reads, symbols, flow,
                        taking(both.left(), true, reads, assumed, symbols), live, each, out);
            }
            case Core.Binary either when either.op() == Hir.BinOp.OR -> {
                walk(either.left(), plan, reads, symbols, flow, assumed, live, each, out);
                walk(either.right(), plan, reads, symbols, flow,
                        taking(either.left(), false, reads, assumed, symbols), live, each, out);
            }
            // The condition under what stood above the fork, and each arm under what that arm proves
            // of it. A comparison inside a condition is not below the fork: it runs to decide it.
            case Core.If iff -> {
                walk(iff.cond(), plan, reads, symbols, flow, assumed, live, each, out);
                walk(iff.then(), plan, reads, symbols, flow,
                        taking(iff.cond(), true, reads, assumed, symbols), live, each, out);
                walk(iff.els(), plan, reads, symbols, flow,
                        taking(iff.cond(), false, reads, assumed, symbols), live, each, out);
            }
            // What a `let` computes is read on the way to the answer only where the name is read;
            // everywhere else a value stands in a body it is consumed by what it stands in. And its
            // body is where the name stands for what was bound to it.
            case Core.LetIn let -> {
                walk(let.value(), plan, reads, symbols, flow, assumed,
                        live && flow.reads(let), each, out);
                walk(let.body(), plan, reads.and(let.binder(), let.value()), symbols, flow, assumed,
                        live, each, out);
            }
            // What runs inside a function value runs once per application, and how many applications
            // there are is the caller's to say. Where the caller is an operation over a container and
            // this is the step it applies per element, the elements are what it applies it to and the
            // input walk has a position for one of them.
            case Core.Block step -> walk(step.body(), plan, reads, symbols, flow, assumed, live,
                    each && perElement(step, reads, symbols), out);
            default -> Core.forEachChild(e, child ->
                    walk(child, plan, reads, symbols, flow, assumed, live, each, out));
        }
    }

    /**
     * Whether {@code step} is applied once per element of a container, which is what makes its
     * applications occurrences of one position rather than an unknown number of passes.
     *
     * <p>Read off the binding of the parameter the elements arrive at, which is what
     * {@link souther.compiler.check.ElementBindings} recorded where the operation is written. Not
     * read off the shape of the call here: after the rewrite that fuses the walks there is no call
     * left to match, and a reading that matched one would narrow with nothing saying so.
     */
    private static boolean perElement(Core.Block step, InputReads reads, Symbols symbols) {
        // Applied once per element of the container the parameter is handed elements of, and each
        // of those elements at a position the input walk names. A container the walk names nothing
        // at is one no row can be read at, so what repeats there is still a number of passes and not
        // a number of occurrences, and a line drawn on it would be owed by nothing.
        for (Hir.Binder param : step.params()) {
            if (param.binding() != null && reads.elementAt(param.binding(), symbols) != null) {
                return true;
            }
        }
        return false;
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
}
