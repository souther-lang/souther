package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.DateTranslation;
import souther.compiler.types.ValueName;
import souther.runtime.ConstraintViolation;
import souther.runtime.Temporals;
import souther.test.ClosedWorldContract;

import java.time.LocalDate;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * An operation the library declares as a date and a count of days is a shift, and a shift is read
 * as defined wherever the date it answers is one.
 *
 * <p>What is declared of such an operation is the form of its answer, and that says nothing of
 * where the program stops. A chain of them keeps where every step is defined
 * ({@link DateTranslation}) on the assumption that a step stops at the end of the calendar and
 * nowhere else. So the operations read that way are listed here, and each is run: an operation
 * declared tomorrow as a shift is one this names until somebody has held it to the same.
 */
@ClosedWorldContract
class EveryOperationReadAsAShiftOfADateStopsOnlyWhereItsResultIsNoDateTest {

    private static final long FIRST = LocalDate.MIN.toEpochDay();
    private static final long LAST = LocalDate.MAX.toEpochDay();

    @Test
    void theOperationsReadAsAShiftAreTheOnesRunBelow() {
        Set<ValueName> read = DefaultBoundOperationFacts.get().answersAFormOfItsArguments().stream()
                .filter(DateShifts::isAShift).collect(Collectors.toSet());

        assertEquals(Set.of(ValueName.Stdlib.operation("Date", "addDays")), read,
                "an operation read as a shift of a date is one whose run time is held below to"
                        + " stop only where its result is no date");
    }

    private static LocalDate addDays(LocalDate date, long days) {
        try {
            return Temporals.addDays(date, days);
        } catch (ConstraintViolation _) {
            return null;
        }
    }

    /**
     * Run on dates at each end of the calendar and a day inside it, shifted by amounts that stay
     * inside, reach the end exactly and go past it, and chained so that a step undone is one the
     * first of them stops at.
     */
    @Test
    void addDaysStopsWhereTheTranslationSaysItIsNotDefined() {
        List<LocalDate> dates = List.of(LocalDate.MIN, LocalDate.MIN.plusDays(1),
                LocalDate.of(2026, 1, 1), LocalDate.MAX.minusDays(1), LocalDate.MAX);
        long[] amounts = {0, 1, -1, 366, -366, LAST - FIRST, FIRST - LAST, Long.MAX_VALUE,
                Long.MIN_VALUE};
        for (LocalDate date : dates) {
            for (long first : amounts) {
                for (long second : amounts) {
                    LocalDate once = addDays(date, first);
                    LocalDate twice = once == null ? null : addDays(once, second);
                    DateTranslation chain = DateTranslation.none().thenAddDays(first);
                    chain = chain == null ? null : chain.thenAddDays(second);

                    boolean defined = chain != null && chain.definedAt(date.toEpochDay());
                    assertEquals(defined, twice != null,
                            date + " shifted by " + first + " and then " + second);
                    if (defined) {
                        assertEquals(date.toEpochDay() + chain.offsetDays(),
                                twice.toEpochDay());
                    }
                }
            }
        }
    }
}
