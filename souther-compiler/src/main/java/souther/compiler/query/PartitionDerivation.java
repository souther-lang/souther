package souther.compiler.query;

import souther.compiler.observe.FailureReason;
import souther.compiler.observe.NotApplicableReason;
import souther.compiler.partition.ClosureGap;
import souther.compiler.partition.MeasureClosure;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * What the partition measure came to over one behavior.
 *
 * <p>A {@link Measurement} of the positions it is measured at. It was a sum of its own with five
 * arms, each mirroring one state of a measurement and none of them carrying what made it that state:
 * {@code Partial} held the positions it found and nothing about the reading that stopped, and
 * {@code Unresolved} held nothing at all — while the four facts that produced either sat in a list
 * beside the measure, where every reader had to go and rebuild the answer from them (issue #953).
 *
 * <p><b>Which reading is asked is this measure's own.</b> Not "every reader ran to the end": which
 * readers there are is a fact about this compiler, and a completeness written off them moves when
 * one is added. The closure is over the questions the model raised that this measure answers
 * ({@code CoverageObligation.answeredBy}), so a rule whose line nothing could read leaves the border
 * measure short and this one whole.
 *
 * <p><b>{@link NothingIsDivided} is a conclusion and still costs a proof to say.</b> It takes the
 * closure of this measure's own reading, which only {@code souther.compiler.partition} can produce.
 * The sentence "the model divides nothing anywhere and no row would change that" is the one that
 * must not be cheap to write, since it is what takes a behavior out of the verdict — so the proof
 * moved onto the reason rather than being dropped when the arms became a measurement's.
 */
public final class PartitionDerivation {

    private PartitionDerivation() {}

    /**
     * Every question this measure answers was answered, and the model divides no position of this
     * behavior into classes.
     *
     * <p>Nothing here for the measure to be about. A plain {@code String}, an {@code Int} no rule
     * cuts, a {@code List} whose elements were reached and have no rule about them: no row an author
     * writes puts a class there, and only editing the model would. Counted in the verdict, one such
     * behavior held every model it appears in open for a measurement that was never anybody's to
     * make.
     */
    public record NothingIsDivided(MeasureClosure.OfThePartition.Closed proven)
            implements NotApplicableReason {

        public NothingIsDivided {
            java.util.Objects.requireNonNull(proven, "an absence is what a closed reading came to");
        }

        @Override
        public String name() {
            return "NOTHING_IS_DIVIDED";
        }
    }

    /** This behavior has no positions for the measure to be about — a {@code >->} composition,
     *  which is measured at its stages. */
    public enum NoSubject implements NotApplicableReason {
        NO_SUBJECT
    }

    /**
     * The reading of what this measure answers did not run out, so what it did not find is not known
     * not to be there. A rule about a position's values that nothing took in, a position whose rules
     * were never enumerated, a position dropped past the axis limit.
     *
     * <p>What {@code NO_AXIS_DERIVED} said of every empty answer, now said only where it is true —
     * and, since #953, said beside the gaps that make it true rather than on its own.
     */
    public enum TheReadingDidNotRunOut implements FailureReason {
        THE_READING_DID_NOT_RUN_OUT
    }

    /** What a behavior measured at its stages rather than at itself comes to. */
    public static Measurement<List<PartitionEvidence.AxisCoverage>> noSubject() {
        return new Measurement.NotApplicable<>(NoSubject.NO_SUBJECT);
    }

    /**
     * What the measure came to, from what it found and whether its reading ran out.
     *
     * <p>The one place the states are chosen between, so that no caller pairs an answer with
     * evidence it does not go with. Nothing is decided from the shape of {@code at} alone: an empty
     * answer is an absence or a reading that stopped depending on the closure, and a full one is
     * complete or partial by the same fact.
     */
    public static Measurement<List<PartitionEvidence.AxisCoverage>> of(
            List<PartitionEvidence.AxisCoverage> at, MeasureClosure.OfThePartition closure) {
        if (closure instanceof MeasureClosure.OfThePartition.Closed closed) {
            return at.isEmpty()
                    ? new Measurement.NotApplicable<>(new NothingIsDivided(closed))
                    : new Measurement.Complete<>(List.copyOf(at));
        }
        WeakeningSet by = weakening(((MeasureClosure.OfThePartition.Open) closure).by());
        return at.isEmpty()
                ? new Measurement.FailedToMeasure<>(
                        TheReadingDidNotRunOut.THE_READING_DID_NOT_RUN_OUT, by)
                : new Measurement.Partial<>(List.copyOf(at), by);
    }

    /** What an open reading leaves a measurement weaker by. Every gap it found, each as the fact the
     *  reader that found it produced. */
    static WeakeningSet weakening(Set<ClosureGap> gaps) {
        Set<Weakening> out = new LinkedHashSet<>();
        for (ClosureGap gap : gaps) {
            out.add(new Weakening.ModelReadingIncomplete(gap));
        }
        return WeakeningSet.ofAll(out);
    }

    /** The positions this behavior is measured at, empty where the measure has none to show. */
    public static List<PartitionEvidence.AxisCoverage> at(
            Measurement<List<PartitionEvidence.AxisCoverage>> measurement) {
        return measurement.made().orElseGet(List::of);
    }
}
