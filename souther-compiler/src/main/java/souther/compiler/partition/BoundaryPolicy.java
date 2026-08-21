package souther.compiler.partition;

import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.inputs.InputReads;

import java.util.ArrayList;
import java.util.List;

/**
 * Which of a body's comparisons the rules of a model are read off, and why the rest are not.
 *
 * <p><b>The rule, said in what a behavior does rather than in what a body looks like.</b> A
 * comparison is a boundary rule where its truth is on a live flow to what the behavior answers with,
 * and where one run passes it at most once. Nothing about the construct it is written in is part of
 * that. A comparison tested by an {@code if}, given a name a line above the fork that tests it,
 * returned as the behavior's answer, or written into a field of the answer's data is one rule put to
 * four uses, and a model divides its input at the same value in all four — so naming a truth is not
 * a statement about what a model divides, and neither is spelling one out.
 *
 * <p>It was written as {@code directly under a fork, through &&  and ||} because a fork was for a
 * long time the only thing that could measure a comparison: reaching an arm was the evidence that
 * the comparison ran. That made one sentence do two jobs — whether the comparison can be measured,
 * and whether the model states anything by it — and the two came apart the day a comparison got a
 * site of its own. The measurement moved to the comparison and the policy did not, so a
 * meaning-preserving rewrite moved the partition.
 *
 * <p><b>A policy over {@link souther.compiler.coverage.ComparisonCatalog}</b> and not a second
 * account of what a comparison is. The catalog says what the bodies hold; this decides which of
 * those a line is drawn on, and the two are different questions with different answers. Kept apart
 * because the first is a fact about the source and the second is a decision about what a model
 * divides — and while they were one walk, the decision was being made by whatever the numbering
 * happened to reach.
 *
 * <p><b>Total over the body's comparisons.</b> Every one of them is answered for, as a line or as
 * one of {@link NotABoundary}'s reasons, because a comparison left out of a set is one whose absence
 * every later reader has to explain for itself. A filter answers one question; this answers the one
 * the readers actually have, which is what to say about the comparison in front of them.
 *
 * <p>Asked of a comparison and answered for a whole body, which is the shape the question has. Asked
 * of a fork instead, the reader of lines had to find a fork before it could find a rule — so
 * widening what bears a line would have meant rewriting that reader rather than this.
 *
 * <p>What is not answered here is what reaching an arm of a fork proves about a comparison under it.
 * Under {@code A && (B || C)} the arms tell those three apart — the arm the whole condition holds on
 * proves {@code A} ran and {@code B} ran, and proves nothing about {@code C} — and no measure asks: a
 * row meets a line by lighting the comparison's own probe, which is a fact the comparison records for
 * itself. It is a relation between a comparison and one use of its truth, so a comparison consumed by
 * two forks has two answers and one consumed by none has no answer at all. Anything modelling it
 * belongs where the uses are, not here and not on the origin.
 */
final class BoundaryPolicy {

    /**
     * One comparison a line is drawn on, and where the names in it point.
     *
     * <p>The reading travels with the comparison because it is not the same at every one of them: a
     * comparison inside an expanded helper is about the argument the call handed it, and read
     * against the names outside the binding it is about nothing at all.
     */
    record Bearing(Core.Binary comparison, InputReads reads) {}

    /** What this policy says about one comparison of the body. */
    sealed interface Standing {

        /** The comparison this is about, whichever answer it got. */
        Core.Binary comparison();

        /**
         * Where the names in it point.
         *
         * <p>Here rather than only beside a line, because what a comparison says about a position is
         * asked of the ones that bear none too: a rule this could not read is still a rule written
         * at a position, and read against the wrong names it is written at none.
         */
        InputReads reads();

        /** A line is drawn on it, and read under {@code bearing}'s names. */
        record DrawsALine(Bearing bearing) implements Standing {

            @Override
            public Core.Binary comparison() {
                return bearing.comparison();
            }

            @Override
            public InputReads reads() {
                return bearing.reads();
            }
        }

        /** No line is drawn on it, and this is which of the reasons it is. */
        record DrawsNone(Core.Binary comparison, InputReads reads, NotABoundary why)
                implements Standing {}
    }

    private final List<Standing> standing;

    private BoundaryPolicy(List<Standing> standing) {
        this.standing = List.copyOf(standing);
    }

    /** What this says about every comparison of the body, in the order the source wrote them. */
    List<Standing> all() {
        return standing;
    }

    /** The comparisons a line is drawn on, in the order the source wrote them. */
    List<Bearing> drawn() {
        return standing.stream()
                .filter(Standing.DrawsALine.class::isInstance)
                .map(each -> ((Standing.DrawsALine) each).bearing())
                .toList();
    }

    /** What this policy says about each comparison of {@code body}. */
    static BoundaryPolicy of(Core body, CoverageSites.Plan plan, InputReads reads) {
        List<Standing> standing = new ArrayList<>();
        gather(body, plan, reads, LiveFlow.of(body), true, standing);
        return new BoundaryPolicy(standing);
    }

    /**
     * @param live whether what is computed here is read on the way to what the behavior answers
     *             with. Carried down rather than asked at each comparison, because everything inside
     *             a value nothing reads is read by nothing either
     */
    private static void gather(Core e, CoverageSites.Plan plan, InputReads reads, LiveFlow flow,
                               boolean live, List<Standing> standing) {
        if (e instanceof Core.Binary comparison && plan.comparisons().at(comparison).isPresent()) {
            standing.add(standingOf(comparison, plan, reads, live));
        }
        // Inside what a `let` binds, since that is where a name standing for an argument is read as
        // the argument.
        InputReads inside = e instanceof Core.LetIn let ? reads.and(let.binder(), let.value())
                : reads;
        if (e instanceof Core.LetIn let) {
            // What a `let` computes is read on the way to the answer only where the name is read.
            // Everywhere else a value stands in a body it is consumed by what it stands in — a
            // condition decides a fork, an operand is combined, an argument is handed over, a field
            // becomes part of a value, a tail is what the body answers with — so this is the one
            // place a flow stops.
            gather(let.value(), plan, reads, flow, live && flow.reads(let), standing);
            gather(let.body(), plan, inside, flow, live, standing);
            return;
        }
        Core.forEachChild(e, child -> gather(child, plan, inside, flow, live, standing));
    }

    /**
     * What one comparison's standing is.
     *
     * <p>The reason about the model is said first. A comparison the behavior's answer does not turn
     * on is not a boundary whichever way it could have been measured, and a reader told instead that
     * its outcome cannot be attributed to a row would go looking for a way to attribute it.
     */
    private static Standing standingOf(Core.Binary comparison, CoverageSites.Plan plan,
                                       InputReads reads, boolean live) {
        if (!live) {
            return new Standing.DrawsNone(comparison, reads, NotABoundary.NOTHING_READS_IT);
        }
        // Meeting a line takes getting the comparison to answer, and whether it answered is what a
        // site records — so a comparison with no site is one no row could ever be shown to have
        // reached, and a border on it would owe a row nothing can measure.
        if (plan.comparisonAt(comparison).isEmpty()) {
            return new Standing.DrawsNone(comparison, reads, NotABoundary.NOTHING_RECORDS_IT);
        }
        // A recording holds that a place was passed and not how many times, so two outcomes of one
        // comparison in one run cannot be told from two rows' outcomes.
        if (plan.mayRepeat(comparison)) {
            return new Standing.DrawsNone(comparison, reads, NotABoundary.REPEATED_IN_ONE_RUN);
        }
        return new Standing.DrawsALine(new Bearing(comparison, reads));
    }
}
