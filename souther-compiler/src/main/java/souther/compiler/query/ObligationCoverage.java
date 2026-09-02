package souther.compiler.query;

import souther.compiler.observe.MeasureReason;

import java.util.List;
import java.util.Objects;

/**
 * Whether a row is at one point of an authored line, over every reading of that line.
 *
 * <p>Not a {@link Measurement}, and its own type so that it cannot be read as one. A reading's
 * coverage is a measurement of that reading — it may be made in part and still have found a row,
 * because what a reading could not read and what it did find are separate facts about it. A debt's
 * is not: a row found at any reading settles the line ({@link
 * souther.compiler.partition.BorderObligationId}), so the state where something went unread and a
 * row was seen anyway is one this cannot hold, and a reader of a debt has no such state to consider.
 *
 * <p>Four states, and the fold below is the one place they are chosen between.
 */
public sealed interface ObligationCoverage {

    /** A row this compilation observed stands at the point. */
    record Witnessed() implements ObligationCoverage {}

    /** Every reading ran to the end, and no row is at the point. */
    record Missed() implements ObligationCoverage {}

    /**
     * No row was seen, and a reading that could have been holding one did not run to the end.
     *
     * <p>What was not found is undecided rather than absent: the row that answers this point may be
     * in the part nobody read. Never weakened by nothing, for the reason {@link Measurement.Partial}
     * is not — a state that says it is short of something and cannot say what would be the absence
     * of the answer written as an answer.
     */
    record Undecided(WeakeningSet by) implements ObligationCoverage {

        public Undecided {
            if (by == null || by.isEmpty()) {
                throw new IllegalArgumentException(
                        "an obligation left undecided says what left it so");
            }
        }
    }

    /** Nothing was read against this point, and this is why. */
    record NotMeasured(NotMeasuredReason why) implements ObligationCoverage {

        public NotMeasured {
            Objects.requireNonNull(why, "an obligation nobody measured says why");
        }
    }

    /** Whether a row this compilation observed stands at the point. */
    default boolean hasRowWitness() {
        return this instanceof Witnessed;
    }

    /**
     * Whether the readings came to an answer about this point at all.
     *
     * <p>Not what became of the obligation. That is {@link ObligationDisposition}'s, and it reads
     * this beside what has shown a row can be written here: a point read to the end and missed is
     * a gap where something promises a row could stand there and one nobody could decide where
     * nothing does. Neither reading takes the obligation away — what the model owes is settled
     * before either of them.
     */
    default boolean hasAnswer() {
        return !(this instanceof NotMeasured);
    }

    /**
     * Whether that answer is short of nothing, which is what a verdict rests on.
     *
     * <p>What {@link Measurement.Complete} is to a measure. A row found and a point read to the end
     * and missed are both answers; a point left undecided and one nobody read are the two states a
     * build cannot be called satisfied over.
     */
    default boolean settled() {
        return this instanceof Witnessed || this instanceof Missed;
    }

    /** What the readings behind this went without, which is empty unless they left it undecided. */
    default WeakeningSet weakening() {
        return this instanceof Undecided it ? it.by() : WeakeningSet.none();
    }

    /** Why there is no answer, or null where there is one. */
    default MeasureReason why() {
        return this instanceof NotMeasured it ? it.why() : null;
    }

    /**
     * What the readings of one authored line come to together.
     *
     * <p>One debt is read at every position of every behavior carrying the type, and each of those
     * readings measures it on its own. What the debt came to is not any one of them: a row standing
     * at the line through {@code draft.owner} is evidence about {@code UserId}, and the reading at
     * {@code activities[*]@CallTask.owner} cannot disagree with it.
     *
     * <p><b>Here and nowhere else.</b> A report, a build's refusal, an editor and the generator all
     * ask what became of a debt, and four foldings of the same readings would be four answers about
     * one line.
     *
     * <p>The order is the whole of it. A row found settles the line whatever else went unread, so a
     * hit outranks everything. Below that, a reading that could be hiding a row outranks one that
     * ran out and found none, because the second is an answer and the first is the absence of one.
     * And a reading with no rows to look at is neither: it hides nothing, so it cannot take back a
     * miss another reading established, and where every reading is one there was nothing anywhere to
     * look at.
     */
    static ObligationCoverage acrossTheReadings(
            List<Measurement<ItemAssessment.Coverage>> readings) {
        if (readings.isEmpty()) {
            throw new IllegalArgumentException(
                    "a debt is what its readings came to, and this is none of them");
        }
        WeakeningSet unread = WeakeningSet.none();
        NotMeasuredReason unasked = null;
        boolean missed = false;
        for (Measurement<ItemAssessment.Coverage> reading : readings) {
            // Found is found. Said before anything else is looked at, so that no accounting of what
            // went unread can weaken a row somebody wrote.
            if (reading.made().map(ItemAssessment.Coverage::hit).orElse(false)) {
                return new Witnessed();
            }
            switch (reading) {
                // A reading of this line that did not run out. Whatever it could not read may be
                // holding the row.
                case Measurement.Partial<ItemAssessment.Coverage> in -> unread = unread.union(in.by());
                case Measurement.FailedToMeasure<ItemAssessment.Coverage> stopped -> {
                    if (((ItemAssessment.Coverage.CouldNotAsk) stopped.why()).mayHideARow()) {
                        unread = unread.union(stopped.by());
                    }
                }
                // The three reasons a question was not put are not one answer here. One that may be
                // hiding a row is kept as itself rather than turned into a weakening: nothing was
                // read, so there is no reading for a weakening to be about.
                case Measurement.NotMeasured<ItemAssessment.Coverage> none -> {
                    if (((ItemAssessment.Coverage.NotAsked) none.why()).mayHideARow()) {
                        unasked = none.why();
                    }
                }
                // Read to the end and no row is at the point, which is what a miss is.
                case Measurement.Complete<ItemAssessment.Coverage> _ -> missed = true;
            }
        }
        if (!unread.isEmpty()) {
            return new Undecided(unread);
        }
        // Above a miss another reading established, because a reading that looked at nothing leaves
        // the rows it would have looked at unaccounted for. Both of the reasons that reach here are
        // settings of the build rather than facts about one behavior, so this is reached where every
        // reading says it and not where one of them does.
        if (unasked != null) {
            return new NotMeasured(unasked);
        }
        // Every reading had nothing to look at, so neither has the debt.
        return missed ? new Missed()
                : new NotMeasured(ItemAssessment.Coverage.NotAsked.NO_ROWS);
    }

    /**
     * What two searches of one reading of one line saw, as one reading's measurement.
     *
     * <p>For the one place two of those meet: a line read once and searched twice, which is a
     * helper called from two arms. They are not two readings — the authored line and the target are
     * the same, and what differs is the region a row for it was composed in — so what a debt is
     * gathered from has to be one measurement, and this is how the two become it.
     *
     * <p><b>Written in terms of {@link #acrossTheReadings} and not beside it.</b> What a set of
     * measurements comes to is that one's answer, and a second reading of the same question here
     * would be a second coverage semantics free to part from it. So the pair is put through it and
     * the answer is written back as the measurement that says the same thing, which makes
     * {@code acrossTheReadings(a, b)} and {@code acrossTheReadings(across(a, b))} the same answer by
     * construction rather than by two pieces of code being kept in step.
     */
    static Measurement<ItemAssessment.Coverage> acrossOneReadingsSearches(
            Measurement<ItemAssessment.Coverage> a, Measurement<ItemAssessment.Coverage> b) {
        return switch (acrossTheReadings(List.of(a, b))) {
            // A row was seen, and what the searches behind it went without is what both of them
            // went without. Kept as whichever of the two saw it, the answer turned on which was
            // walked first — the one that saw a row and read everything, and the one that saw a row
            // and could not, are one reading here, and what it could not read is a fact of its own.
            case Witnessed _ -> {
                WeakeningSet went = wentWithout(a).union(wentWithout(b));
                yield went.isEmpty()
                        ? new Measurement.Complete<>(new ItemAssessment.Coverage.Hit())
                        : new Measurement.Partial<>(new ItemAssessment.Coverage.Hit(), went);
            }
            case Undecided it -> new Measurement.Partial<>(new ItemAssessment.Coverage.NoHit(),
                    it.weakening());
            case Missed _ -> new Measurement.Complete<>(new ItemAssessment.Coverage.NoHit());
            case NotMeasured it -> new Measurement.NotMeasured<>(it.why());
        };
    }

    /** What one search of a reading could not read, and none where it read everything. */
    private static WeakeningSet wentWithout(Measurement<ItemAssessment.Coverage> made) {
        return switch (made) {
            case Measurement.Partial<ItemAssessment.Coverage> it -> it.by();
            case Measurement.FailedToMeasure<ItemAssessment.Coverage> it -> it.by();
            case Measurement.Complete<ItemAssessment.Coverage> _,
                 Measurement.NotMeasured<ItemAssessment.Coverage> _ -> WeakeningSet.none();
        };
    }
}
