package souther.compiler.partition;

import souther.compiler.check.CoverageObligation;
import souther.compiler.check.RuleAccounting;
import souther.compiler.inputs.StructuralInspection;

import java.util.List;

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
 * <p><b>Closed is a conclusion, and only this package draws it.</b> Each {@code Closed} has a
 * package-private constructor and is reached through {@link #of}, which is handed the whole of what
 * a behavior's reading came to. Outside this package there is no way to make one, so a caller
 * holding one is holding the proof that the reading ran out — the arrangement
 * {@link UndividedPosition.Why.Absent} is under, at the measure rather than at a position.
 *
 * <p><b>The questions first.</b> What a measure is mostly short of is a question the model raised
 * that nothing answered, filed under the measure that answers it
 * ({@link CoverageObligation#answeredBy}). Counted as "every reader ran to the end" instead, a
 * completeness says the model was read in full for exactly as long as nobody adds a reader.
 *
 * <p><b>And three facts no question carries.</b> A position whose rules were never enumerated
 * raises none, and a set of raised questions all answered is what a reading that never looked also
 * produces ({@link Axis#rulesNotReached}). A position past the axis limit was dropped with whatever
 * it was carrying. And a rule the model wrote that this could not use is one whose question a
 * reading may well have answered before the position refused the answer — two clauses placing ends
 * on a {@code String}'s two coordinates are read, accounted for, and then both dropped, and the
 * accounting is right to say they were read. What an accounting cannot say is that the measure was
 * then left with nothing, and that is what this reads the refusals for.
 *
 * <p>Which measures each of the three costs is each one's own answer, and they do not agree. A
 * position whose rules were never enumerated and one the walk could not reach into leave both short,
 * because what is not known about them is not known for either. A dropped axis leaves the partition
 * measure short always and the border measure short only where it was carrying a line — what it was
 * carrying is recorded where it was dropped, since neither kind leaves anything behind to read it
 * off afterwards. And a rule set aside answers through its own reason
 * ({@link souther.compiler.inputs.BlockReason.AboutARule#leavesShort}), which for a comparison
 * relating two positions is neither measure.
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

        /** It did not, so what this measure did not find is not known not to be there. */
        record Open() implements OfThePartition {}
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

        /** It did not. */
        record Open() implements OfTheBorder {}
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
     * @param compared what the body's comparisons raised and what answered each
     * @param omitted positions dropped past the axis limit, which leave both measures short: what
     *                they were carrying went with them and no question stands for it
     * @param refused the rules of the model this reading set aside, each from the reader that did.
     *                Asked which measures it leaves short rather than counted: a comparison relating
     *                two positions is set aside by what it says and not by anything missing here,
     *                and it is the rule's own reason that answers
     *                ({@link souther.compiler.inputs.BlockReason.AboutARule#leavesShort})
     */
    static Both of(List<Axis> axes, List<GuardThresholds.Guards.AtAPosition> compared,
                   List<Partitions.OmittedAxis> omitted,
                   List<souther.compiler.inputs.UnreadRule> refused) {
        java.util.Set<CoverageObligation.Measure> short_ = new java.util.LinkedHashSet<>();
        refused.forEach(each -> short_.addAll(each.why().leavesShort()));
        // A dropped axis, asked which measure lost by it. What it was carrying is recorded where it
        // was dropped, because it cannot be read back afterwards: one that was carrying a line took
        // the border's evidence with it, and one that was only classifying took the partition's.
        // Counted as one fact, a model dropping an axis that divides nothing anybody bounds was
        // held open over a measure it never had.
        boolean partition = !short_.contains(CoverageObligation.Measure.PARTITION)
                && omitted.isEmpty();
        boolean border = !short_.contains(CoverageObligation.Measure.BOUNDARY)
                && omitted.stream().noneMatch(Partitions.OmittedAxis::carriedAnObligation);
        for (Axis axis : axes) {
            // A position whose rules nothing enumerated, and one the walk could not reach into.
            // Neither raises a question, so neither can be short of one — which is why they are
            // asked here and not among the questions.
            if (axis.rulesNotReached() || axis.pending() instanceof StructuralInspection.Blocked) {
                partition = false;
                border = false;
                continue;
            }
            for (RuleAccounting.Unanswered each : axis.unanswered()) {
                switch (each.owed().obligation().answeredBy()) {
                    case PARTITION -> partition = false;
                    case BOUNDARY -> border = false;
                }
            }
        }
        for (GuardThresholds.Guards.AtAPosition each : compared) {
            for (RuleAccounting.Unanswered open : each.accounting().unansweredQuestions()) {
                switch (open.owed().obligation().answeredBy()) {
                    case PARTITION -> partition = false;
                    case BOUNDARY -> border = false;
                }
            }
        }
        return new Both(partition ? new OfThePartition.Closed() : new OfThePartition.Open(),
                border ? new OfTheBorder.Closed() : new OfTheBorder.Open());
    }
}
