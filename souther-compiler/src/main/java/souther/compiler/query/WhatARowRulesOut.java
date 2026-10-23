package souther.compiler.query;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.Place;
import souther.compiler.partition.DrawnBoundary;
import souther.compiler.partition.ObservedInputs;
import souther.compiler.partition.StandingAtAPoint;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Whether a row, as its run read it back, rules out a line beside a border at one reading of it.
 *
 * <p>The one place the question is put. A row offered for a line is weighed by it, and so is a row
 * a search composed and saw run to the rule, before the line it was composed for is said to be one
 * a row arriving can tell apart. Both ask it of the row read back and of the reading's own line:
 * the values a search asked for are what the row was composed for and need not be what it holds,
 * and another reading's line was left by other rows.
 *
 * <p>A row whose run reached no value on the line, or one whose sum the exact arithmetic could not
 * hold, is one nothing here can tell about — neither ruling the line out nor shown to leave it.
 */
final class WhatARowRulesOut {

    private WhatARowRulesOut() {
    }

    /**
     * What the row came to, and where on the line it stands where it rules the line out.
     *
     * @param said whether it settles the line, does not, or could not be told about
     * @param at   the positions the reading names, as the row holds them, where it rules the line
     *             out — and null otherwise
     */
    record Said(Settlement said, Map<NumericTerm, Place> at) {

        Said {
            if ((at != null) != said.settles()) {
                throw new IllegalArgumentException("a row rules a line out at the place it stands,"
                        + " and stands nowhere on a line it does not rule out: " + said + " " + at);
            }
            at = at == null ? null : Collections.unmodifiableMap(new LinkedHashMap<>(at));
        }
    }

    /**
     * What {@code row} does to {@code beside}, the line one reading's rows leave beside the border
     * that reading drew as {@code drawn}, read where {@code toRows} reads that reading's line.
     *
     * <p>Whether the row leaves no place on the line standing beside the rows already read, and not
     * whether it answers the line at its current place differently. A row the model keeps between the
     * two ends of a range does the second and not the first: the line moves to it, and the next run
     * finds the same line standing.
     */
    static Said of(StandingAtAPoint.AtALine toRows, DrawnBoundary drawn,
                   AnotherLineTheRowsAllow.Stands beside, ObservedInputs row) {
        StandingAtAPoint.RowsRead read = toRows.valuesOf(List.of(row));
        if (read.each().isEmpty()) {
            // The row holds no value on this line at all, whether because nothing watched its
            // run or because its positions could not be read there. Which of those it is is
            // the reading's own answer and is what a reader is told.
            return new Said(read.everyOne() ? new Settlement.DoesNotSettle()
                    : new Settlement.Undetermined(read.unwatched()
                            ? Settlement.Reason.NO_ACCOUNT_OF_THE_RUN
                            : Settlement.Reason.THE_VALUES_COULD_NOT_BE_READ), null);
        }
        boolean unheld = false;
        for (Map<NumericTerm, Place> values : read.each()) {
            ExactAnswer<Boolean> rules = beside.ruledOutBy(drawn, values);
            if (rules instanceof ExactAnswer.Unheld<Boolean>) {
                unheld = true;
                continue;
            }
            if (((ExactAnswer.Held<Boolean>) rules).value()) {
                return new Said(new Settlement.Settles(), values);
            }
        }
        // A row whose sum could not be held is a row read in part (a reading's own
        // ReadingGap.CouldNotWorkOut), and a row read short of a value is what this answers
        // in that word wherever else a row is put to a line.
        return new Said(unheld
                ? new Settlement.Undetermined(Settlement.Reason.THE_VALUES_COULD_NOT_BE_READ)
                : new Settlement.DoesNotSettle(), null);
    }
}
