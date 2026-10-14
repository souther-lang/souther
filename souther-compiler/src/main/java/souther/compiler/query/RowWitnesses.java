package souther.compiler.query;

import souther.compiler.observe.Disposition;
import souther.compiler.observe.RowOutcome;
import souther.compiler.observe.RowRef;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

/**
 * Which rows a covered obligation is covered by, said as far as what an author does next turns on
 * it.
 *
 * <p>A row that does not hold still ran, so it is evidence of what it went through and an obligation
 * it reached is met. What that leaves an author to know is whether the obligation would still be met
 * without it: correcting or deleting such a row takes coverage away only where no other row covers
 * the same thing. So the rows are kept while every one of them is a row that does not hold, and the
 * first row of any other kind ends the account — which rows those were stops mattering there.
 *
 * <p><b>Another row is not a row that held.</b> It is any row the measure counted that did not fail:
 * one that held, one still waiting for its answer, one recorded before there was a body to run. What
 * this answers is whether the rows that do not hold are all there is, and whether what the rows
 * expected was produced is {@code verified}'s question, not this one's.
 *
 * <p><b>Which rows, and not where they are written.</b> A measure's answer holds no place: where a
 * row is written is looked up where a report is assembled, the way an arm's place is, and an answer
 * keyed on the identity alone is not one an edit that only moves text has to make again.
 */
public sealed interface RowWitnesses {

    /**
     * Every row that covers the obligation is a row that does not hold, and these are they.
     *
     * @param witnesses in the order they were met, and never none: an obligation nothing covers has
     *                  no witnesses at all
     */
    record OnlyRowsThatDoNotHold(Set<RowRef> witnesses) implements RowWitnesses {

        public OnlyRowsThatDoNotHold {
            if (witnesses == null || witnesses.isEmpty()) {
                throw new IllegalArgumentException(
                        "an obligation covered only by rows that do not hold names them");
            }
            witnesses = Collections.unmodifiableSet(new LinkedHashSet<>(witnesses));
        }
    }

    /** A row that is not one that does not hold covers the obligation too. */
    record AnotherRow() implements RowWitnesses {}

    RowWitnesses ANOTHER_ROW = new AnotherRow();

    /**
     * What one row is as a witness: a row that does not hold, or another.
     *
     * <p>The one place a row's disposition is read for this. Which rows a measure counts is the
     * measure's, and this says nothing about it — it is asked only of a row the measure has already
     * counted.
     */
    static RowWitnesses of(RowOutcome row) {
        return row.disposition() == Disposition.FAILED
                ? new OnlyRowsThatDoNotHold(Set.of(RowRef.of(row)))
                : ANOTHER_ROW;
    }

    /** What two sets of witnesses of one obligation come to together. Another row on either side
     *  is another row of both. */
    default RowWitnesses and(RowWitnesses other) {
        if (this instanceof OnlyRowsThatDoNotHold(Set<RowRef> mine)
                && other instanceof OnlyRowsThatDoNotHold(Set<RowRef> theirs)) {
            Set<RowRef> both = new LinkedHashSet<>(mine);
            both.addAll(theirs);
            return new OnlyRowsThatDoNotHold(both);
        }
        return ANOTHER_ROW;
    }

    /** Whether some row other than one that does not hold covers the obligation, which is where
     *  looking further at the rows can change nothing. */
    default boolean anotherRow() {
        return this instanceof AnotherRow;
    }
}
