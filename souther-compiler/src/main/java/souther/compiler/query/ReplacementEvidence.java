package souther.compiler.query;

import souther.compiler.observe.MeasureReason;
import souther.compiler.observe.RowIdentity;
import souther.compiler.partition.Replacement;
import souther.compiler.partition.ReplacementOwed;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

/**
 * What a behavior's rows establish about the rewrites of its body: for each, whether a row tells it
 * from the body as written.
 *
 * <p>Beside the arms and not one of them. A row goes through an arm whatever the arm answers, so
 * every arm can be reached by rows none of which would fail if the arm were written as its sibling;
 * and a body with no fork in it has no arm to reach while its rows can all answer one value. What
 * this measures is whether what the rows state depends on what the body says, which reaching it does
 * not show.
 *
 * <p>Only where there is a body. A behavior answered by something this module does not write has no
 * body to rewrite, and its rows are measured at every other axis as they always were — this adds an
 * axis to an implemented behavior and takes none from an injected one.
 *
 * @param measured the rewrites and what the rows came to about each, or why there are none
 */
public record ReplacementEvidence(Measure<ReplacementEvidence.Summary> measured) {

    public ReplacementEvidence {
        Objects.requireNonNull(measured, "a measure says what it found or why it found nothing");
    }

    /** Why no rewrite was put to the rows, where nobody asked for it to be. */
    public enum NotAsked implements NotMeasuredReason {
        /** The build did not ask for the rows to be run again under a rewrite, which costs a run
         *  per arm a row goes through and sibling it has. */
        NOT_ASKED,
        /** No row names this behavior. */
        NO_ROWS;

        @Override
        public MeasureReason.About about() {
            return switch (this) {
                case NOT_ASKED -> MeasureReason.About.THE_RUN;
                case NO_ROWS -> MeasureReason.About.THE_BEHAVIOR;
            };
        }
    }

    /** Why there is no body here to rewrite. */
    public enum NoBody implements NotApplicableReason {
        /** A {@code >->} composition or a behavior with no {@code let}. */
        NO_BODY;

        @Override
        public MeasureReason.About about() {
            return MeasureReason.About.THE_BEHAVIOR;
        }
    }

    /** The body the rewrites are of is not in the image the run was measured in. */
    public enum BodyWasNotRead implements FailureReason {
        BODY_WAS_NOT_READ;

        @Override
        public MeasureReason.About about() {
            return MeasureReason.About.THE_BEHAVIOR;
        }
    }

    /** The rows ran without the classes that carry the rewrites, so none could be put to them. */
    public enum Unreadable implements FailureReason {
        UNREADABLE;

        @Override
        public MeasureReason.About about() {
            return MeasureReason.About.THE_BEHAVIOR;
        }
    }

    /** Every rewrite of the body and what the rows came to about it, in the reading's order. */
    public record Summary(List<Rewrite> rewrites) {

        public Summary {
            rewrites = List.copyOf(rewrites);
        }

        /** The rewrites some row tells from the body. */
        public long noticed() {
            return rewrites.stream().filter(each -> each.outcome() instanceof Noticed).count();
        }

        /** The rewrites shown to answer differently that no row tells from the body. */
        public long unnoticed() {
            return rewrites.stream().filter(each -> each.outcome() instanceof Unnoticed).count();
        }

        /** The rewrites nothing here could decide about. */
        public long undecided() {
            return rewrites.stream().filter(each -> each.outcome() instanceof Undecided).count();
        }
    }

    /** One rewrite and what the rows came to about it. */
    public record Rewrite(Replacement replacement, Outcome outcome) {

        public Rewrite {
            Objects.requireNonNull(replacement, "a rewrite is some rewrite");
            Objects.requireNonNull(outcome, "a rewrite says what the rows came to about it");
        }
    }

    /** What the rows came to about one rewrite. */
    public sealed interface Outcome permits Noticed, Unnoticed, Undecided {}

    /** A row's statement fails of the rewrite: the row tells it from the body. */
    public record Noticed(RowIdentity by) implements Outcome {

        public Noticed {
            Objects.requireNonNull(by, "a row noticed it");
        }
    }

    /**
     * The rewrite answers some row differently from the body, and no row's statement fails of it.
     * A gap: writing down the answer of the row that shows it is a row that would.
     */
    public record Unnoticed(ShownBy shownBy, ReplacementOwed lookFor) implements Outcome {

        public Unnoticed {
            Objects.requireNonNull(shownBy, "a rewrite shown to matter was shown by some row");
            Objects.requireNonNull(lookFor, "and is one a row telling it apart can be looked for");
        }
    }

    /** Which row shows a rewrite answering differently from the body. */
    public sealed interface ShownBy {

        /** A row the module writes: its run under the rewrite answered differently. */
        record AWrittenRow(RowIdentity row) implements ShownBy {

            public AWrittenRow {
                Objects.requireNonNull(row, "a written row is some row");
            }
        }

        /** A row this compiler composed and ran under both, written as it would be offered. */
        record AComposedRow(List<String> inputs) implements ShownBy {

            public AComposedRow {
                inputs = List.copyOf(inputs);
            }
        }
    }

    /** Nothing here could say whether a row tells the rewrite from the body, and why. */
    public record Undecided(Why why) implements Outcome {

        public Undecided {
            Objects.requireNonNull(why, "a rewrite left open was left open for a reason");
        }

        /** Why a rewrite was left open. */
        public enum Why {
            /** Carrying the sibling would grow the fork past what the classes allow. */
            TOO_LARGE,
            /** No row answered with a value read in full. */
            NOTHING_ANSWERED,
            /** A row states an answer this could not read. */
            A_STATEMENT_WAS_NOT_READ,
            /** Every row the search composed was answered alike by the rewrite and the body.
             *  Not that every input is: the search looked where it looked. */
            NO_ROW_ANSWERED_DIFFERENTLY,
            /** The search stopped with rows it had not tried. */
            THE_SEARCH_STOPPED,
            /** No row the search could look at was composed. */
            NOTHING_WAS_COMPOSED,
            /** Nothing could run a row. */
            NOTHING_RAN
        }
    }

    /** The behavior has no body of its own. */
    public static ReplacementEvidence noBody() {
        return new ReplacementEvidence(new Measure.NotApplicable<>(NoBody.NO_BODY));
    }

    /** Nobody asked for the rewrites to be put to the rows. */
    public static ReplacementEvidence notAsked(NotAsked why) {
        return new ReplacementEvidence(new Measurement.NotMeasured<>(why));
    }

    /** The model says this behavior writes a body and the image the run was measured in does not
     *  carry it. */
    public static ReplacementEvidence bodyNotInEvaluation(String behavior) {
        return new ReplacementEvidence(new Measurement.FailedToMeasure<>(
                BodyWasNotRead.BODY_WAS_NOT_READ,
                WeakeningSet.of(new Weakening.BodyNotInEvaluation(behavior))));
    }

    /** The rows ran without the classes that carry the rewrites. */
    public static ReplacementEvidence unreadable(WeakeningSet by) {
        return new ReplacementEvidence(new Measurement.FailedToMeasure<>(Unreadable.UNREADABLE, by));
    }

    /**
     * The rewrites and what the rows came to about each. Weaker than complete where some rows were
     * not read, and where some rewrite was left open: neither leaves a gap, and both leave the
     * verdict waiting on something.
     */
    public static ReplacementEvidence measured(String behavior, List<Rewrite> rewrites,
                                               WeakeningSet rowsBehind) {
        Summary summary = new Summary(rewrites);
        List<Weakening> open = new ArrayList<>(rowsBehind.causes());
        for (Rewrite each : rewrites) {
            if (each.outcome() instanceof Undecided(Undecided.Why why)) {
                open.add(new Weakening.RewriteUndecided(behavior, each.replacement(), why));
            }
        }
        WeakeningSet by = WeakeningSet.ofAll(open);
        return new ReplacementEvidence(by.isEmpty()
                ? new Measurement.Complete<>(summary)
                : new Measurement.Partial<>(summary, by));
    }

    /** Whether this behavior has a body for the measure to be about. */
    public boolean applicable() {
        return !(measured instanceof Measure.NotApplicable<Summary>);
    }
}
