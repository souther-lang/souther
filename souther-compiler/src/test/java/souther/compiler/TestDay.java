package souther.compiler;

import souther.compiler.numeric.Today;
import souther.test.WrittenOn;

import java.time.LocalDate;

/**
 * The day every test of this module writes rows on ({@link WrittenOn}), as a compilation is told it
 * and as a reading is handed it.
 */
public final class TestDay {

    /** The day itself. */
    public static final LocalDate DATE = WrittenOn.DAY;

    /** The same day, as a reading is handed it. */
    public static final Today TODAY = new Today(DATE);

    private TestDay() {
    }
}
