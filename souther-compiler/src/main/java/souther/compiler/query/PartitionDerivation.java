package souther.compiler.query;

import souther.compiler.observe.MeasureReason;
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

        /** The word, held where a reader with no instance can find it. A reason that costs a proof
         *  to say cannot be an enum, and its word is still the schema's to be held against. */
        public static final String WORD = "NOTHING_IS_DIVIDED";

        public NothingIsDivided {
            java.util.Objects.requireNonNull(proven, "an absence is what a closed reading came to");
        }

        @Override
        public String name() {
            return WORD;
        }

        @Override
        public MeasureReason.About about() {
            return MeasureReason.About.THE_BEHAVIOR;
        }
    }

    /** This behavior has no positions for the measure to be about — a {@code >->} composition,
     *  which is measured at its stages. */
    public enum NoSubject implements NotApplicableReason {
        NO_SUBJECT;

        @Override
        public MeasureReason.About about() {
            return MeasureReason.About.THE_BEHAVIOR;
        }
    }

    /**
     * The reading of what this measure answers did not run out, so what it did not find is not known
     * not to be there. A rule about a position's values that nothing took in, or a position whose
     * rules were never enumerated.
     *
     * <p>What {@code NO_AXIS_DERIVED} said of every empty answer, now said only where it is true —
     * and, since #953, said beside the gaps that make it true rather than on its own.
     */
    public enum TheReadingDidNotRunOut implements FailureReason {
        THE_READING_DID_NOT_RUN_OUT;

        @Override
        public MeasureReason.About about() {
            return MeasureReason.About.THE_BEHAVIOR;
        }
    }

    /**
     * Nothing read the body, so what its rules divide the positions into was never asked.
     *
     * <p>Its own reason and not {@link TheReadingDidNotRunOut}. That one is a reading that was made
     * and stopped on something, and it comes with what it stopped on; this is the reading not
     * having been made, which names nothing and would be reported beside no gap at all. Said as the
     * first, a reader is told a question was raised about this model and there is none to go and
     * look at.
     *
     * <p>What did not read it is not here. A module whose bodies were all refused and one whose
     * implementation this image left out are the same absence to a measure, and which of them it
     * was is the elaboration's answer rather than this measure's.
     */
    public enum BodyWasNotRead implements FailureReason {
        BODY_WAS_NOT_READ;

        @Override
        public MeasureReason.About about() {
            return MeasureReason.About.THE_BEHAVIOR;
        }
    }

    /** What a behavior measured at its stages rather than at itself comes to. */
    public static Measure<List<PartitionEvidence.AxisCoverage>> noSubject() {
        return new Measure.NotApplicable<>(NoSubject.NO_SUBJECT);
    }

    /**
     * What the measure came to, from what it found and whether its reading ran out.
     *
     * <p>The one place the states are chosen between, so that no caller pairs an answer with
     * evidence it does not go with. Nothing is decided from the shape of {@code at} alone: an empty
     * answer is an absence or a reading that stopped depending on the closure, and a full one is
     * complete or partial by the same fact.
     */
    public static Measure<List<PartitionEvidence.AxisCoverage>> of(
            List<PartitionEvidence.AxisCoverage> at, MeasureClosure.OfThePartition closure,
            souther.compiler.inputs.EmptyInput inputIsEmpty) {
        // Before anything about what was found. A class is a set of values a row can be written at,
        // and where the rules leave the input none there is nothing for this measure to be about —
        // which is not the same as the reading having fallen short of one, and not a gap any row
        // could fill. Read from the one proof the behavior carries rather than concluded here, so
        // that this measure and the border beside it cannot answer it two ways.
        if (inputIsEmpty != null) {
            return new Measure.NotApplicable<>(new NoFeasibleInput(inputIsEmpty));
        }
        // A switch over the three a closure has, so a way of not having run out that nobody has
        // decided about here is a compile error rather than whichever arm a cast happened to take.
        return switch (closure) {
            case MeasureClosure.OfThePartition.Closed closed -> at.isEmpty()
                    ? new Measure.NotApplicable<>(new NothingIsDivided(closed))
                    : new Measurement.Complete<>(List.copyOf(at));
            // Nothing read the body, so the classes here are what the declarations and the clauses
            // came to and nothing says what the rules of the body add to them. Not the arm above:
            // an empty answer there is the model dividing this position no way, which is a claim
            // about rules nobody read. Not the one below either — that one names the questions a
            // reading left, and a reading nobody made left none.
            case MeasureClosure.OfThePartition.BodyNotRead unread -> {
                // What it went without is the reading, said as the one weakening there is for a
                // body nothing elaborated. Not a question about a rule: a reading nobody made met
                // none, and naming one would send a reader to a subject nothing looked at.
                // What it went without: the reading of the body, and whatever the readings that
                // were made found beside it. Those are theirs to name and are not about the body.
                WeakeningSet without = WeakeningSet.of(
                        new Weakening.BodiesNotElaborated(unread.module()))
                        .union(PartitionDerivation.weakening(unread.besides()));
                yield at.isEmpty()
                        ? new Measurement.FailedToMeasure<>(
                                BodyWasNotRead.BODY_WAS_NOT_READ, without)
                        : new Measurement.Partial<>(List.copyOf(at), without);
            }
            case MeasureClosure.OfThePartition.Open open -> {
                WeakeningSet by = weakening(open.by());
                yield at.isEmpty()
                        ? new Measurement.FailedToMeasure<>(
                                TheReadingDidNotRunOut.THE_READING_DID_NOT_RUN_OUT, by)
                        : new Measurement.Partial<>(List.copyOf(at), by);
            }
        };
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
            Measure<List<PartitionEvidence.AxisCoverage>> measurement) {
        return measurement.made().orElseGet(List::of);
    }
}
