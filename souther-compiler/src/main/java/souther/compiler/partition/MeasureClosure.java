package souther.compiler.partition;

import souther.compiler.check.CoverageObligation;
import souther.compiler.check.RuleAccounting;
import souther.compiler.inputs.StructuralInspection;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * Whether the reading one measure of coverage depends on came to an end.
 *
 * <p>Two types and not one value shared between them, because the two measures are short of
 * different things. A rule whose line nothing could read leaves the border measure short while the
 * classes either side of it were read in full; a walk that never reached a position's rules leaves
 * both short. Written as one answer about the behavior, the first case reports the partition
 * measure on the strength of what stopped the other one — and the day a third measure arrives it
 * inherits whatever the two of them happened to share.
 *
 * <p><b>Closed is a conclusion, and only this class draws it.</b> Each {@code Closed} has a private
 * constructor and is reached through {@link #of}, which is handed the whole of what a behavior's
 * reading came to. Nowhere else is there a way to make one, so a caller holding one is holding the
 * proof that the reading ran out — the arrangement {@link UndividedPosition.Why.Absent} is under, at
 * the measure rather than at a position.
 *
 * <p><b>The questions first.</b> What a measure is mostly short of is a question the model raised
 * that nothing answered, filed under the measure that answers it
 * ({@link CoverageObligation#answeredBy}). Counted as "every reader ran to the end" instead, a
 * completeness says the model was read in full for exactly as long as nobody adds a reader.
 *
 * <p><b>And two facts no question carries.</b> A position whose rules were never enumerated
 * raises none, and a set of raised questions all answered is what a reading that never looked also
 * produces ({@link Axis#rulesNotReached}). And a rule the model wrote that this could not use is one
 * whose question a reading may well have answered before the position refused the answer — two
 * clauses placing ends on a {@code String}'s two coordinates are read, accounted for, and then
 * both dropped, and the accounting is right to say they were read. What an accounting cannot say
 * is that the measure was then left with nothing, and that is what this reads the refusals for.
 *
 * <p>Which measures each of the two costs is each one's own answer, and they do not agree. A
 * position whose rules were never enumerated and one the walk could not reach into leave both short,
 * because what is not known about them is not known for either. And a rule set aside answers
 * through its own reason ({@link souther.compiler.inputs.BlockReason.RuleWithoutLineReason#leavesShort}),
 * which for a comparison relating two positions is neither measure.
 *
 * <p><b>A clause's question may stand and a comparison's may not.</b> A comparison raises a question
 * exactly where the reading of it reached a line, and that line answers it — both come off the one
 * reading, so a comparison either yields the question and its answer together or yields neither and
 * records what stopped it. So the way a comparison leaves a measure short is as a rule this reading
 * set aside, and never as a question nothing answered.
 */
public final class MeasureClosure {

    private MeasureClosure() {}

    /** Whether the partition measure's reading ran out. */
    public sealed interface OfThePartition {

        /**
         * It did: every question this measure answers was accounted for, everywhere.
         *
         * <p>Two of these are one conclusion and compare equal. Costing something to say is about
         * who may say it and not about which instance said it — an answer that never equals its own
         * recomputation is one {@code Db} reports as changed on every run, and everything that read
         * it runs again over a model nobody edited. {@link UndividedPosition.Why.Absent} carries
         * the same pair for the same reason.
         */
        final class Closed implements OfThePartition {

            private Closed() {}

            @Override
            public boolean equals(Object other) {
                return other instanceof Closed;
            }

            @Override
            public int hashCode() {
                return Closed.class.hashCode();
            }

            @Override
            public String toString() {
                return "PartitionClosed";
            }
        }

        /**
         * It did not, and this is what was still open when it stopped.
         *
         * <p>Never empty. Something has to have been found for the reading not to have run out, so
         * an open closure carrying nothing is a measure that would come back weaker than complete
         * with no account of why — which is the whole of issue #953.
         */
        record Open(Set<ClosureGap> by) implements OfThePartition {

            public Open {
                by = gaps(by);
            }
        }
    }

    /** Whether the border measure's reading ran out. The same question of the other measure, and a
     *  separate type so that neither can be answered with the other's answer. */
    public sealed interface OfTheBorder {

        /** It did, and two of these are one conclusion — see {@link OfThePartition.Closed}. */
        final class Closed implements OfTheBorder {

            private Closed() {}

            @Override
            public boolean equals(Object other) {
                return other instanceof Closed;
            }

            @Override
            public int hashCode() {
                return Closed.class.hashCode();
            }

            @Override
            public String toString() {
                return "BorderClosed";
            }
        }

        /** It did not, and this is what was still open. Never empty, for the reason
         *  {@link OfThePartition.Open} gives. */
        record Open(Set<ClosureGap> by) implements OfTheBorder {

            public Open {
                by = gaps(by);
            }
        }
    }

    /** What the two closures come to, together, so that neither is built from half a reading. */
    record Both(OfThePartition partition, OfTheBorder border) {}

    /**
     * What each measure's reading came to over one behavior.
     *
     * <p>Everything the reading could be short of arrives here at once. Asked measure by measure
     * afterwards, the two would be built from whatever their caller had in hand at the time, which
     * is the second bookkeeping this type exists to prevent.
     *
     * @param axes    every position the reading kept, measured or not
     * @param refused the rules of the model this reading set aside, each from the reader that did.
     *                Asked which measures it leaves short rather than counted: a comparison relating
     *                two positions is set aside by what it says and not by anything missing here,
     *                and it is the rule's own reason that answers
     *                ({@link souther.compiler.inputs.BlockReason.RuleWithoutLineReason#leavesShort})
     */
    static Both of(List<Axis> axes, List<souther.compiler.inputs.RuleWithoutALine> refused) {
        Set<ClosureGap> partition = new LinkedHashSet<>();
        Set<ClosureGap> border = new LinkedHashSet<>();
        for (souther.compiler.inputs.RuleWithoutALine rule : refused) {
            if (rule.why().leavesShort(CoverageObligation.Measure.PARTITION)) {
                partition.add(new ClosureGap.RuleUnread(rule));
            }
            if (rule.why().leavesShort(CoverageObligation.Measure.BOUNDARY)) {
                border.add(new ClosureGap.RuleUnread(rule));
            }
        }
        for (Axis axis : axes) {
            // A position whose rules nothing enumerated, and one the walk could not reach into.
            // Neither raises a question, so neither can be short of one — which is why they are
            // asked here and not among the questions.
            boolean unreached = false;
            if (axis.rulesNotReached()) {
                ClosureGap gap = new ClosureGap.RulesNotReached(axis.id());
                partition.add(gap);
                border.add(gap);
                unreached = true;
            }
            if (axis.pending() instanceof StructuralInspection.Continuation.Blocked blocked) {
                ClosureGap gap = new ClosureGap.PositionNotReachedInto(axis.id(), blocked.why());
                partition.add(gap);
                border.add(gap);
                unreached = true;
            }
            if (unreached) {
                continue;
            }
            for (RuleAccounting.Unanswered each : axis.unanswered()) {
                ClosureGap gap = new ClosureGap.QuestionUnanswered(axis.id(), each);
                switch (each.owed().obligation().answeredBy()) {
                    case PARTITION -> partition.add(gap);
                    case BOUNDARY -> border.add(gap);
                }
            }
        }
        return new Both(
                partition.isEmpty() ? new OfThePartition.Closed() : new OfThePartition.Open(partition),
                border.isEmpty() ? new OfTheBorder.Closed() : new OfTheBorder.Open(border));
    }

    /** An open closure's own account of itself: never empty, and in the order the readers found it,
     *  so that two runs over one model produce the same value. */
    private static Set<ClosureGap> gaps(Set<ClosureGap> by) {
        if (by == null || by.isEmpty()) {
            throw new IllegalArgumentException(
                    "a reading that did not run out has something it did not get to");
        }
        return Collections.unmodifiableSet(new LinkedHashSet<>(by));
    }
}
