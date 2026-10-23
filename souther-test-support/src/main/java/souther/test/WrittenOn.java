package souther.test;

import java.time.LocalDate;

/**
 * The day every test of every module writes generated rows on, so that a date a rule leaves free
 * comes out the same whatever day the suite runs.
 */
public final class WrittenOn {

    /** The day itself. */
    public static final LocalDate DAY = LocalDate.of(2026, 10, 23);

    private WrittenOn() {
    }
}
