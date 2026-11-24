package souther.compiler.semantics;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.DateTranslation;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.ValueTransformation;

import java.time.LocalDate;
import java.util.List;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where a part of a date lies over the dates between two ends, and the run of it each number of
 * which one of those dates gives, held to the numbers the dates give counted one at a time.
 *
 * <p>Every run of dates from each of a few starts — the first of a year, the last day of one, the
 * end of February in a leap year and in a common one, the first and the last dates there are — up
 * to a little over a year long, moved by nothing, a day back, a day on and a year back. Where the
 * part lies holds every number a date gives. The run each number of which is given is given whole,
 * and is the least to the most where the numbers given leave no gap.
 */
class APartOfADateBetweenEndsIsWhatItsDatesGiveTest {

    private static final List<LocalDate> STARTS = List.of(
            LocalDate.of(1900, 1, 1), LocalDate.of(1899, 12, 31), LocalDate.of(2000, 2, 27),
            LocalDate.of(2023, 2, 27), LocalDate.of(2020, 12, 30), LocalDate.MIN,
            LocalDate.MAX.minusDays(400));

    private static final List<Integer> LENGTHS = List.of(0, 1, 2, 3, 30, 31, 32, 60, 300, 364,
            365, 366, 400);

    private static final List<Long> MOVES = List.of(0L, -1L, 1L, -365L);

    @Test
    void eachPartIsWhatTheDatesBetweenTheEndsGive() {
        for (TakenAs.DatePart part : TakenAs.DatePart.values()) {
            TakenAs.PartOfDate taken = new TakenAs.PartOfDate(part);
            for (LocalDate start : STARTS) {
                for (int length : LENGTHS) {
                    LocalDate end = start.plusDays(Math.min(length,
                            LocalDate.MAX.toEpochDay() - start.toEpochDay()));
                    for (long move : MOVES) {
                        DateTranslation chain = DateTranslation.none().thenAddDays(move);
                        ValueTransformation from = move == 0 ? new ValueTransformation.Identity()
                                : new ValueTransformation.DateShift(chain);
                        held(taken, from, chain, start, end);
                    }
                }
            }
        }
    }

    private static void held(TakenAs.PartOfDate taken, ValueTransformation from,
                             DateTranslation chain, LocalDate start, LocalDate end) {
        TreeSet<Integer> given = new TreeSet<>();
        for (long day = start.toEpochDay(); day <= end.toEpochDay(); day++) {
            if (chain.definedAt(day)) {
                given.add(taken.part().of(LocalDate.ofEpochDay(day + chain.offsetDays())));
            }
        }
        NumericDomain.Bounds days = new NumericDomain.Bounds(
                Endpoint.inclusive(Count.of(start.toEpochDay())),
                Endpoint.inclusive(Count.of(end.toEpochDay())));
        String asked = taken.part() + " of " + start + " to " + end + " moved by " + chain;

        NumericDomain.Bounds lies = taken.reachedFrom(from, days);
        NumericDomain.Bounds whole = taken.answeredWholeFrom(from, days);
        if (given.isEmpty()) {
            assertNull(whole, asked);
            return;
        }
        for (int each : given) {
            assertTrue(lies.admits(Count.of(each)), asked + ": " + each + " lies outside " + lies);
        }
        boolean noGap = given.last() - given.first() + 1 == given.size();
        if (noGap) {
            assertEquals(new NumericDomain.Bounds(Endpoint.inclusive(Count.of(given.first())),
                    Endpoint.inclusive(Count.of(given.last()))), whole, asked + ": " + given);
        } else if (whole != null) {
            for (int number = whole.min().at() instanceof Count low ? low.at().intValueExact() : 0;
                    whole.admits(Count.of(number)); number++) {
                assertTrue(given.contains(number), asked + ": " + number + " is no date's, "
                        + given);
            }
        }
    }
}
