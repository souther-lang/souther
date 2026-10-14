package souther.compiler.query;

import souther.compiler.observe.Figure;
import souther.compiler.observe.MeasureReason;
import souther.compiler.observe.RowRef;
import souther.compiler.observe.RunSensitivity;
import souther.compiler.publish.CanonicalSelection;
import souther.compiler.publish.PublicationOrders;
import souther.compiler.observe.RowIdentity;
import souther.compiler.partition.Replacement;
import souther.compiler.partition.ReplacementOwed;

import java.util.ArrayList;
import java.util.Collection;
import java.util.EnumMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

/**
 * What a behavior's rows establish about the rewrites of its body: for each, whether a row tells it
 * from the body as written.
 *
 * <p>Beside the arms and not one of them. A row goes through an arm whatever the arm answers, so
 * every arm can be reached by rows none of which would come out differently were the arm written
 * as its sibling;
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

    /** One rewrite, where a report about it is shown, and what the rows came to about it. */
    public record Rewrite(ReplacementAsWritten written, ReplacementReportAnchor reportAt,
                          Outcome outcome) {

        public Rewrite {
            Objects.requireNonNull(written, "a rewrite is some rewrite");
            Objects.requireNonNull(reportAt, "and is shown somewhere");
            Objects.requireNonNull(outcome, "a rewrite says what the rows came to about it");
            if (!reportAt.shows(written.replacement())) {
                throw new IllegalArgumentException(written + " is not shown at " + reportAt);
            }
        }

        /** Which rewrite this is. */
        public Replacement replacement() {
            return written.replacement();
        }
    }

    /** What the rows came to about one rewrite. */
    public sealed interface Outcome permits Noticed, Unnoticed, Undecided {}

    /** A row comes out the other way under the rewrite: the row tells it from the body. */
    public record Noticed(RowIdentity by) implements Outcome {

        public Noticed {
            Objects.requireNonNull(by, "a row noticed it");
        }
    }

    /**
     * The rewrite answers some row differently from the body, and no row comes out differently
     * under it.
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

        /**
         * A row the module writes: its run under the rewrite answered differently.
         *
         * @param rowRef which row, with the source it is written in: a row written without a name
         *               is numbered within its source, and two sources each have a first row.
         *               Where it is written is asked by whoever sends a reader there
         */
        record AWrittenRow(RowRef rowRef) implements ShownBy {

            public AWrittenRow {
                Objects.requireNonNull(rowRef, "a written row is some row");
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
    public record Undecided(LeftOpen why) implements Outcome {

        /**
         * Every way it was left open, and not the one that ranks first: a search that ran out of
         * runs and stopped composing besides was stopped by two figures, and a reader raising one
         * of them is owed the other. In the order they are published in.
         */
        public Undecided {
            Objects.requireNonNull(why, "a rewrite left open was left open for a reason");
        }

        public Undecided(Collection<Way> ways) {
            this(LeftOpen.of(ways));
        }

        public Undecided(Way way) {
            this(List.of(way));
        }

        /**
         * Every way one rewrite was left open, one per reason, in the order the reasons are
         * published in.
         *
         * <p>A reason met more than once is one way, holding every figure any of its meetings was
         * stopped at. Where one of them was met at something no run allows — the host's limit —
         * that is what the way is: a wider run meets it again whatever else it gets past.
         */
        public record LeftOpen(List<Way> ways) {

            public LeftOpen {
                ways = List.copyOf(ways);
                if (ways.isEmpty()) {
                    throw new IllegalArgumentException(
                            "a rewrite left open was left open for a reason");
                }
            }

            /** {@code met}, one way per reason, in the order the reasons are published in. */
            public static LeftOpen of(Collection<Way> met) {
                Map<Why, List<Way>> byReason = new EnumMap<>(Why.class);
                for (Way each : met) {
                    byReason.computeIfAbsent(each.why(), _ -> new ArrayList<>()).add(each);
                }
                List<Way> out = new ArrayList<>();
                for (Why reason : PublicationOrders.REWRITE_UNDECIDED_REASONS
                        .keep(byReason.keySet()).written()) {
                    out.add(Way.together(reason, byReason.get(reason)));
                }
                return new LeftOpen(out);
            }

            /** The reasons, in the order they are published in. */
            public CanonicalSelection<Why> reasons() {
                return PublicationOrders.REWRITE_UNDECIDED_REASONS.keep(
                        ways.stream().map(Way::why).toList());
            }

            /** Never: a rewrite left open was left open for a reason. */
            public boolean isEmpty() {
                return ways.isEmpty();
            }

            /** Every figure any way was stopped at, each once, in the order of the ways. */
            public List<Figure> figures() {
                Set<Figure> out = new LinkedHashSet<>();
                ways.forEach(each -> out.addAll(each.figures()));
                return List.copyOf(out);
            }

            /** Whether a wider run could come to another answer: where any way of it could. */
            public RunSensitivity runSensitivity() {
                return ways.stream().anyMatch(
                        each -> each.runSensitivity() == RunSensitivity.MAY_CHANGE)
                        ? RunSensitivity.MAY_CHANGE : RunSensitivity.UNAFFECTED;
            }
        }

        /**
         * One way a rewrite was left open, as the place that left it open found it.
         *
         * <p>Whether a wider run gets past it is the place's to say and not the reason's: a fork too
         * large to carry its siblings is held to a figure of this compiler's, and a method too large
         * for the JVM is held to the host's, and both are published as one reason.
         */
        public sealed interface Way {

            /** The reason it is published as. */
            Why why();

            /** The figures it was stopped at, as each stood where it was reached; none exactly
             *  where nothing it was stopped at is a figure of this compiler's. */
            List<Figure> figures();

            /** Whether a run that allows more could get past it. */
            RunSensitivity runSensitivity();

            /** Several meetings of one reason as one way: at no allowance where any of them is, and
             *  otherwise at every figure any of them was stopped at. */
            private static Way together(Why why, List<Way> met) {
                if (met.stream().anyMatch(AtNoAllowance.class::isInstance)) {
                    return new AtNoAllowance(why);
                }
                Set<Figure> figures = new LinkedHashSet<>();
                met.forEach(each -> figures.addAll(each.figures()));
                return new AtFigures(why, List.copyOf(figures));
            }

            /**
             * Stopped at figures this compiler holds its work to, each carried from where it was
             * reached: a run allowing more of them gets further.
             */
            record AtFigures(Why why, List<Figure> figures) implements Way {

                public AtFigures {
                    Objects.requireNonNull(why, "a way left open is published as some reason");
                    figures = Figure.inOrder(figures);
                    if (figures.isEmpty()) {
                        throw new IllegalArgumentException(
                                "a way stopped at figures names one: " + why);
                    }
                }

                @Override
                public RunSensitivity runSensitivity() {
                    return RunSensitivity.MAY_CHANGE;
                }
            }

            /**
             * Left open by nothing a run allows: what the rows came to, or a limit of the host's.
             * Every run of this compiler over this model leaves it open the same way, so there is
             * no figure to name.
             */
            record AtNoAllowance(Why why) implements Way {

                public AtNoAllowance {
                    Objects.requireNonNull(why, "a way left open is published as some reason");
                }

                @Override
                public List<Figure> figures() {
                    return List.of();
                }

                @Override
                public RunSensitivity runSensitivity() {
                    return RunSensitivity.UNAFFECTED;
                }
            }
        }

        /** Why a rewrite was left open. */
        public enum Why {
            /** Carrying the sibling would grow the fork past what the classes allow. */
            TOO_LARGE,
            /** A row states an answer this could not read, or neither held nor failed of the body
             *  as written. */
            A_STATEMENT_WAS_NOT_READ,
            /** Every row the search composed was answered alike by the rewrite and the body.
             *  Not that every input is: the search looked where it looked. */
            NO_ROW_ANSWERED_DIFFERENTLY,
            /** The search made as many runs as the measure lets one rewrite take, with rows left. */
            RUNS_SPENT,
            /** Composing the rows the search looked through stopped at a figure of its own. */
            A_COMPOSING_FIGURE_REACHED,
            /** A run the search asked for came back without an answer it could read. */
            A_RUN_DID_NOT_COME_BACK,
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
            if (each.outcome() instanceof Undecided(Undecided.LeftOpen why)) {
                open.add(new Weakening.RewriteUndecided(behavior, each.replacement(), why));
            }
        }
        WeakeningSet by = WeakeningSet.ofAll(open);
        return new ReplacementEvidence(by.isEmpty()
                ? new Measurement.Complete<>(summary)
                : new Measurement.Partial<>(summary, by));
    }

    /**
     * One rewrite as the measure read it. What reading it went without is what the rows did, and
     * not that another rewrite was left open: that bears on the other one and on no other.
     */
    public record OfOneRewrite(Rewrite rewrite, WeakeningSet weakening) {

        public OfOneRewrite {
            Objects.requireNonNull(rewrite, "a reading of one rewrite is of some rewrite");
            Objects.requireNonNull(weakening, "and says what it went without, or that it went"
                    + " without nothing");
        }
    }

    /** Every rewrite the measure read, each with what reading it went without; none where it has
     *  no value. */
    public List<OfOneRewrite> each() {
        Optional<Summary> made = measured.made();
        if (made.isEmpty()) {
            return List.of();
        }
        List<Weakening> rowsBehind = new ArrayList<>();
        for (Weakening cause : measured.weakening().causes()) {
            if (!(cause instanceof Weakening.RewriteUndecided)) {
                rowsBehind.add(cause);
            }
        }
        WeakeningSet behind = WeakeningSet.ofAll(rowsBehind);
        List<OfOneRewrite> out = new ArrayList<>();
        for (Rewrite rewrite : made.get().rewrites()) {
            out.add(new OfOneRewrite(rewrite, behind));
        }
        return List.copyOf(out);
    }

    /** Whether this behavior has a body for the measure to be about. */
    public boolean applicable() {
        return !(measured instanceof Measure.NotApplicable<Summary>);
    }
}
