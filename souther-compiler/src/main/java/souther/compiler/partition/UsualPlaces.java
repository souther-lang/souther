package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Today;
import souther.compiler.numeric.UsualPlace;
import souther.compiler.semantics.TakenAs;

import java.time.LocalDate;

/**
 * Where each number a row writes is usually near, decided in one place for every reader that
 * chooses one.
 *
 * <p>A value of a position is near where its order is ({@link Carrier#usualPlace}): a date at
 * today, a date-time and a moment at the start of it. The year of a date is near today's year,
 * between the first and the last year the calendar has. Nothing else a row writes has a place it
 * is usually near — a count starts at nought, and a month or a day of a month runs over a
 * handful of numbers every one of which a reader writes.
 */
final class UsualPlaces {

    private UsualPlaces() {
    }

    /** Where a value for {@code term}, counted on {@code carrier}, is usually near on
     *  {@code today}. */
    static UsualPlace of(NumericTerm term, Carrier carrier, Today today) {
        return switch (term) {
            // A value of the position, or the value at an end of its key: a place on the
            // position's own order.
            case NumericTerm.ValueOf _, NumericTerm.ExtremeOfItsKey _ ->
                    carrier.usualPlace(today);
            // A step of a coarser order is a place on that order, so it is near where that order is:
            // the day a date-time falls on is near today.
            case NumericTerm.WholeUnitsOf _ -> carrier.usualPlace(today);
            case NumericTerm.TakenOf taken -> ofWhatIsTaken(taken.takenAs(), today);
            // Counts and totals of what a value holds, which start at nought.
            case NumericTerm.CodePointClassCount _, NumericTerm.CodePointValueSum _,
                 NumericTerm.CodePointAt _,
                 NumericTerm.GatheredUnderItsKey _, NumericTerm.GatheredUnderAKey _,
                 NumericTerm.TakenOver _, NumericTerm.Multiplicity _,
                 NumericTerm.OccurrencesOfItsValue _, NumericTerm.OccurrencesOfAKey _,
                 NumericTerm.ProductOf _ -> UsualPlace.NONE;
        };
    }

    /** Where a number an operation takes of a value is usually near: the year of a date near
     *  today's, and nothing else anywhere. */
    private static UsualPlace ofWhatIsTaken(TakenAs how, Today today) {
        return switch (how) {
            case TakenAs.PartOfDate(TakenAs.DatePart part) ->
                    part == TakenAs.DatePart.YEAR ? ofAYear(today) : UsualPlace.NONE;
            case TakenAs.PartOfTime _, TakenAs.HowManyItHolds _, TakenAs.TheSumOfWhatItHolds _,
                 TakenAs.TheTruncatingQuotient _, TakenAs.TheFloorRemainder _ -> UsualPlace.NONE;
        };
    }

    /** Where the year of a date is usually near: today's. */
    static UsualPlace ofAYear(Today today) {
        return new UsualPlace.Near(Count.of(today.year()), Count.of(LocalDate.MIN.getYear()),
                Count.of(LocalDate.MAX.getYear()));
    }
}
