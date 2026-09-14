package souther.compiler.query;

import souther.compiler.observe.MeasureReason;
import souther.compiler.partition.Generator;
import souther.compiler.partition.InteractionRequirements;
import souther.compiler.partition.ObligationIdentity;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;

/**
 * The combinations one behavior's body settles a value by, and which of them the rows were seen
 * making.
 *
 * <p>Two halves and one value, for the reason {@link DecisionEvidence} holds its two: what
 * combinations there are is read off the body alone, and what meets one is a run that made the
 * decisions. Held apart, a reader would be free to put one body's combinations beside another's
 * runs.
 *
 * <p>The second half is a measure like every other. Which combinations the rows made can go unasked,
 * come back unreadable, or come back read in part — and a combination nothing was seen making under
 * any of those is not a combination nothing covers.
 *
 * @param asked what the body's meetings ask of the rows
 * @param made  which of them the rows were seen making, and how far that reading got
 */
public record InteractionEvidence(InteractionRequirements asked, Measure<RowsMeeting> made) {

    public InteractionEvidence {
        Objects.requireNonNull(asked, "a behavior's combinations are some reading's");
        Objects.requireNonNull(made, "there is always an answer to what the rows made");
    }

    /**
     * The combinations no row was seen making, where the rows were read at all.
     *
     * <p>Empty where no reading was made, which is not every combination being met: what a
     * combination nothing read is owed is unknown, and a list of all of them would be read as a
     * list of gaps. A caller asks {@link #made()} whether there was a reading first.
     */
    public List<ObligationIdentity.OfACombinationOfDecisions> notMadeByRows() {
        if (made.made().isEmpty()) {
            return List.of();
        }
        Set<ObligationIdentity.OfACombinationOfDecisions> met = made.made().orElseThrow().met();
        return asked.ways().keySet().stream().filter(each -> !met.contains(each)).toList();
    }

    /** How many combinations the body has, which is what the count beside it is out of. */
    public int counted() {
        return asked.ways().size();
    }

    /**
     * What every row of the behavior came to, against the combinations.
     *
     * <p>Three states and every row is in one. A row whose run was read either made some of the
     * combinations or made none of them; a row nothing watched says nothing about any of them — and
     * the third is not the second, because a run with no account did not fail to meet anything, it
     * did what nothing recorded.
     *
     * <p>Held to adding up, so that a row cannot go missing between the rows read and what is
     * counted here.
     *
     * @param rowsRead       how many rows this reading was given
     * @param met            the combinations some row was seen making
     * @param rowsWatched    how many rows carried an account of their run
     * @param rowsNotWatched rows nothing watched, which is this compiler's shortfall and not
     *                       anything about the model
     */
    public record RowsMeeting(int rowsRead, Set<ObligationIdentity.OfACombinationOfDecisions> met,
                              int rowsWatched, int rowsNotWatched) {

        public RowsMeeting {
            met = Collections.unmodifiableSet(new LinkedHashSet<>(met));
            if (rowsWatched < 0 || rowsNotWatched < 0) {
                throw new IllegalArgumentException(
                        "rows are counted from none: " + rowsWatched + "/" + rowsNotWatched);
            }
            if (rowsWatched + rowsNotWatched != rowsRead) {
                throw new IllegalArgumentException("a reading of " + rowsRead
                        + " rows accounted for " + (rowsWatched + rowsNotWatched) + " of them");
            }
        }

        /** Whether every row of the behavior was one something watched. */
        public boolean everyRowWasWatched() {
            return rowsNotWatched == 0;
        }
    }

    /**
     * What the rows made of {@code asked}, read off what each of them was watched doing.
     *
     * <p>Existential over the rows and over the ways to a combination: a combination some run made
     * is made, and a run that took one of the two places a body records it did what the combination
     * asks. Which is the whole of the reading — nothing here says a row does not meet one, because
     * a row that met none of them is evidence about that row and not about the combinations.
     *
     * <p><b>A row nothing watched weakens the reading.</b> Such a row may be the row that makes a
     * combination nothing else does, so a measurement that called itself complete over the rows it
     * could see would hand the account a gap a written row already fills — and a build is entitled
     * to refuse over a gap. Said here rather than left to the reading of the rows, for the reason
     * the rules' measure says it: a row with no account can sit in a reading of the rows that
     * finished.
     */
    public static InteractionEvidence of(String behavior, InteractionRequirements asked,
                                         List<Generator.Watched> watched,
                                         WeakeningSet weakening) {
        Set<ObligationIdentity.OfACombinationOfDecisions> met = new LinkedHashSet<>();
        int seen = 0;
        List<Generator.Watched.Ran> ran = new ArrayList<>();
        for (Generator.Watched each : watched) {
            if (each instanceof Generator.Watched.Ran run) {
                seen++;
                ran.add(run);
            }
        }
        for (ObligationIdentity.OfACombinationOfDecisions item : asked.ways().keySet()) {
            for (Generator.Watched.Ran run : ran) {
                if (asked.met(item, claim -> claim.satisfiedBy(run.seen()))) {
                    met.add(item);
                    break;
                }
            }
        }
        RowsMeeting rows =
                new RowsMeeting(watched.size(), met, seen, watched.size() - seen);
        WeakeningSet went = rows.everyRowWasWatched() ? weakening
                : weakening.union(WeakeningSet.of(
                        new Weakening.DecisionRunNotWatched(behavior)));
        return new InteractionEvidence(asked, went.isEmpty()
                ? new Measurement.Complete<>(rows) : new Measurement.Partial<>(rows, went));
    }

    /**
     * Why nobody read which combinations the rows made, where nothing went wrong in the reading.
     *
     * <p>A behavior no row names is not one of these. A reading over no rows is a reading that was
     * made: it finds that no combination was met, which is what an author writing the first row of
     * that behavior is told.
     */
    public enum NotAsked implements NotMeasuredReason {

        /** The build does not run rows with the instrumentation a place is recorded by. */
        NOT_ASKED;

        @Override
        public MeasureReason.About about() {
            return MeasureReason.About.THE_RUN;
        }
    }

    /**
     * Why a reading that was asked for and started came back with nothing.
     *
     * <p>Each of these leaves what the rows meet unknown rather than empty. A combination nothing
     * was seen making under one of them is one a row may already meet, so no account may call it
     * missing and nothing may refuse over it.
     */
    public enum Unreadable implements FailureReason {

        /** Rows are written for this behavior and none of them came back to be read. */
        NO_ROW_CAME_BACK,

        /** The rows ran without the instrumentation a place is recorded by, so they carry no run to
         *  put against a combination. */
        THE_ROWS_CARRY_NO_ACCOUNT;

        @Override
        public MeasureReason.About about() {
            return MeasureReason.About.THE_BEHAVIOR;
        }
    }
}
