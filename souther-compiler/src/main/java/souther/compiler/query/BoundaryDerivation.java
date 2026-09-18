package souther.compiler.query;


import souther.compiler.observe.MeasureReason;
import souther.compiler.partition.MeasureClosure;

import java.util.List;

/**
 * What the border measure came to over one behavior: a {@link Measurement} of the lines it found.
 *
 * <p>The counterpart of {@link PartitionDerivation} and a separate reading, because the two measures
 * are short of different things. A rule whose line nothing could read leaves this one short while
 * the classes either side of it were read in full.
 *
 * <p>{@link NoRuleDrawsALine} costs a proof to say, for the reason
 * {@link PartitionDerivation.NothingIsDivided} gives.
 */
public final class BoundaryDerivation {

    private BoundaryDerivation() {}

    /**
     * Every question this measure answers was answered, and no rule of the model draws a line
     * anywhere on this behavior's positions.
     *
     * <p>A row cannot make a line. What draws one is a rule — an invariant's bound, a {@code guard}'s
     * comparison — so a behavior over an enumeration nothing bounds has no line for a row to be at
     * and no row that could put one there. That is nothing for the measure to be about, and counting
     * it held the module's verdict open for as long as the behavior existed.
     */
    public record NoRuleDrawsALine(MeasureClosure.OfTheBorder.Closed proven)
            implements NotApplicableReason {

        /** The word, for the reason {@link PartitionDerivation.NothingIsDivided#WORD} gives. */
        public static final String WORD = "NO_RULE_DRAWS_A_LINE";

        public NoRuleDrawsALine {
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

    /** This behavior has no positions for a line to be drawn on — a {@code >->} composition, which
     *  is measured at its stages. */
    public enum NoSubject implements NotApplicableReason {
        NO_SUBJECT;

        @Override
        public MeasureReason.About about() {
            return MeasureReason.About.THE_BEHAVIOR;
        }
    }

    /**
     * The reading of what this measure answers did not run out. A rule that places an end and could
     * not be turned into a line, or a position whose rules were never reached.
     *
     * <p>What {@code NO_LINES_DERIVED} said of every empty answer. It was made {@code NOT_MEASURED}
     * because nothing could tell a model whose bounds sit one type away from a model with no bound
     * at all; the closure tells them apart, and this is what is left of the first.
     */
    public enum TheReadingDidNotRunOut implements FailureReason {
        THE_READING_DID_NOT_RUN_OUT;

        @Override
        public MeasureReason.About about() {
            return MeasureReason.About.THE_BEHAVIOR;
        }
    }

    /**
     * Nothing read the body, so what lines its own rules draw was never asked.
     *
     * <p>This measure's own, for the reason every reason here is: what a reader does about a border
     * measure that is short of a reading is not what they do about a partition one, and a word
     * shared between them would be one sentence for two pieces of work. The same fact behind both,
     * and the same distinction from {@link TheReadingDidNotRunOut}: that one was made and stopped
     * on something it can name.
     */
    public enum BodyWasNotRead implements FailureReason {
        BODY_WAS_NOT_READ;

        @Override
        public MeasureReason.About about() {
            return MeasureReason.About.THE_BEHAVIOR;
        }
    }

    /** What a behavior measured at its stages rather than at itself comes to. */
    public static Measure<List<BorderAssessment>> noSubject() {
        return new Measure.NotApplicable<>(NoSubject.NO_SUBJECT);
    }

    /** What the measure came to, from what it found and whether its reading ran out. The one place
     *  the states are chosen between. */
    public static Measure<List<BorderAssessment>> of(List<BorderAssessment> at,
                                                         MeasureClosure.OfTheBorder closure,
                                                         souther.compiler.inputs.EmptyInput
                                                                 inputIsEmpty) {
        // The same answer the partition beside it gives, from the same proof. A point of a line is a
        // value a row stands at, and where the rules leave the input none there is no row to ask
        // for — read here rather than concluded, so the two measures cannot disagree about one
        // model.
        if (inputIsEmpty != null) {
            return new Measure.NotApplicable<>(new NoFeasibleInput(inputIsEmpty));
        }
        // A switch over the three, for the reason the partition beside it is one.
        return switch (closure) {
            case MeasureClosure.OfTheBorder.Closed closed -> {
                if (at.isEmpty()) {
                    yield new Measure.NotApplicable<>(new NoRuleDrawsALine(closed));
                }
                WeakeningSet beside = whatHoldingThemAgainstTheirNeighboursWentWithout(at);
                yield beside.isEmpty() ? new Measurement.Complete<>(List.copyOf(at))
                        : new Measurement.Partial<>(List.copyOf(at), beside);
            }
            // Nothing read the body. What a closed border with nothing at it says is that no rule
            // of this model draws a line, and one rule of a body draws a line at every number it
            // names — so answering that here would prove it off a reading nobody made.
            case MeasureClosure.OfTheBorder.BodyNotRead unread -> {
                // What it went without: the reading of the body, and whatever the readings that
                // were made found beside it. Those are theirs to name and are not about the body.
                WeakeningSet without = WeakeningSet.of(
                        new Weakening.BodyNotInEvaluation(unread.behavior()))
                        .union(PartitionDerivation.weakening(unread.besides()));
                yield at.isEmpty()
                        ? new Measurement.FailedToMeasure<>(
                                BodyWasNotRead.BODY_WAS_NOT_READ, without)
                        : new Measurement.Partial<>(List.copyOf(at), without.union(
                                whatHoldingThemAgainstTheirNeighboursWentWithout(at)));
            }
            case MeasureClosure.OfTheBorder.Open open -> {
                WeakeningSet by = PartitionDerivation.weakening(open.by());
                yield at.isEmpty()
                        ? new Measurement.FailedToMeasure<>(
                                TheReadingDidNotRunOut.THE_READING_DID_NOT_RUN_OUT, by)
                        : new Measurement.Partial<>(List.copyOf(at),
                                by.union(whatHoldingThemAgainstTheirNeighboursWentWithout(at)));
            }
        };
    }

    /**
     * What holding these lines against the lines beside them went without.
     *
     * <p>Part of this measure and not a measure of its own, because it is the same value: an
     * assessment of a line answers what a row stands at each of its points and what the rows leave
     * standing beside it, and a reading that came back short of the second is a reading of these
     * lines that came back short. What is missing is said in words of its own
     * ({@link Weakening.ABorderNotHeldAgainstTheLinesBesideIt}), so a reader is told which of the
     * two questions fell short rather than being left to read it off the measure's name.
     *
     * <p>Empty for every settled answer, whichever way it settled and however few rows it took. A
     * walk short of a row that left no line standing has established that, because reading more
     * rows leaves fewer lines standing and never more — so being short is not what makes this
     * partial, and coming back unsettled is.
     */
    private static WeakeningSet whatHoldingThemAgainstTheirNeighboursWentWithout(
            List<BorderAssessment> at) {
        WeakeningSet out = WeakeningSet.none();
        for (BorderAssessment line : at) {
            out = out.union(line.besideWeakening());
        }
        return out;
    }

    /** The lines this behavior is measured at, empty where the measure has none to show. */
    public static List<BorderAssessment> at(Measure<List<BorderAssessment>> measurement) {
        return measurement.made().orElseGet(List::of);
    }
}
