package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.runtime.ConstraintViolation;

import java.time.LocalDate;
import java.time.LocalDateTime;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A shift off the end of what a temporal can hold aborts, and says so in the language's own terms.
 *
 * <p>These called {@code java.time} directly, so {@code Date.addYears(999999999, d)} reached the
 * boundary as {@code java.time.DateTimeException: Invalid value for Year (valid values -999999999
 * - 999999999)} and {@code addDays} with a large enough count as
 * {@code java.lang.ArithmeticException: long overflow}. Both name a class the language has no type
 * for, at a program that never mentioned one.
 *
 * <p>Running out of range is the same kind of thing as an {@code Int} overflow — not a business
 * result, and not the infrastructure being unavailable either (ADR-0029) — so it aborts, as an
 * invariant violation does, and the abort says what it was doing.
 */
class CalendarArithmeticOffTheEndOfTheRangeAbortsTest {

    private static final String MODEL = """
            module demo

            data In = { n: Int }
            data OutDate = { d: Date }
            data OutMoment = { at: DateTime }

            behavior years : (i: In) -> OutDate constructs OutDate
            let years (i) = OutDate { d = Date.addYears(i.n, Date("2026-01-01")) }

            behavior months : (i: In) -> OutDate constructs OutDate
            let months (i) = OutDate { d = Date.addMonths(i.n, Date("2026-01-01")) }

            behavior days : (i: In) -> OutDate constructs OutDate
            let days (i) = OutDate { d = Date.addDays(i.n, Date("2026-01-01")) }

            behavior minutes : (i: In) -> OutMoment constructs OutMoment
            let minutes (i) = OutMoment { at = DateTime.addMinutes(i.n, DateTime("2026-01-01T00:00")) }

            behavior hours : (i: In) -> OutMoment constructs OutMoment
            let hours (i) = OutMoment { at = DateTime.addHours(i.n, DateTime("2026-01-01T00:00")) }

            behavior momentDays : (i: In) -> OutMoment constructs OutMoment
            let momentDays (i) = OutMoment { at = DateTime.addDays(i.n, DateTime("2026-01-01T00:00")) }
            """;

    /** Every shift, run past what its temporal holds. Walked rather than sampled: each of the six was
     *  its own call straight into {@code java.time}, so one left wrapped is one that still leaks. */
    @Test
    void everyShiftAbortsRatherThanLettingJavaTimeOut() throws Exception {
        BytesClassLoader loader = load();
        for (String behavior : List.of("years", "months", "days", "minutes", "hours", "momentDays")) {
            Throwable cause = abortOf(loader, behavior, Long.MAX_VALUE);
            assertInstanceOf(ConstraintViolation.class, cause,
                    behavior + " aborted with " + cause.getClass().getName() + ": " + cause.getMessage());
            assertTrue(cause.getMessage().contains("outside the range it can hold"),
                    behavior + ": " + cause.getMessage());
            assertTrue(cause.getMessage().contains("2026-01-01"),
                    behavior + " names the value it was shifting: " + cause.getMessage());
        }
    }

    /** The year range is the one `java.time` refuses at, and it is reached long before a count
     *  overflows — the two ways out that used to surface as two different JVM classes. */
    @Test
    void theYearRangeAndTheCountOverflowAreOneAbort() throws Exception {
        BytesClassLoader loader = load();
        for (long count : List.of(999_999_999L, Long.MAX_VALUE)) {
            assertInstanceOf(ConstraintViolation.class, abortOf(loader, "years", count),
                    "years by " + count);
        }
    }

    /** What still answers, so the wrapping is not a shift that stopped working. */
    @Test
    void aShiftInsideTheRangeStillAnswers() throws Exception {
        BytesClassLoader loader = load();
        assertEquals(LocalDate.parse("2027-01-01").toString(),
                String.valueOf(field(run(loader, "years", 1), "d")));
        assertEquals(LocalDate.parse("2026-02-01").toString(),
                String.valueOf(field(run(loader, "months", 1), "d")));
        assertEquals(LocalDate.parse("2025-12-31").toString(),
                String.valueOf(field(run(loader, "days", -1), "d")));
        assertEquals(LocalDateTime.parse("2026-01-01T00:01").toString(),
                String.valueOf(field(run(loader, "minutes", 1), "at")));
        assertEquals(LocalDateTime.parse("2026-01-01T01:00").toString(),
                String.valueOf(field(run(loader, "hours", 1), "at")));
        assertEquals(LocalDateTime.parse("2026-01-02T00:00").toString(),
                String.valueOf(field(run(loader, "momentDays", 1), "at")));
    }

    /** What the shift threw, unwrapped from the reflection that invoked it. */
    private static Throwable abortOf(BytesClassLoader loader, String behavior, long n) {
        Exception thrown = assertThrows(Exception.class, () -> run(loader, behavior, n),
                behavior + " must not answer for a shift it cannot make");
        for (Throwable t = thrown; t != null; t = t.getCause()) {
            if (t instanceof ConstraintViolation) {
                return t;
            }
        }
        return thrown;
    }

    private static BytesClassLoader load() throws Exception {
        return new BytesClassLoader(Compiler.compile(MODEL),
                CalendarArithmeticOffTheEndOfTheRangeAbortsTest.class.getClassLoader());
    }

    private static Map<?, ?> run(BytesClassLoader loader, String behavior, long n) throws Exception {
        String out = List.of("minutes", "hours", "momentDays").contains(behavior)
                ? "demo.OutMoment" : "demo.OutDate";
        Object in = Codecs.decoded(loader, "demo.In", Map.of("n", n));
        Object answered = Codecs.apply(
                Emitted.behavior(loader, "demo", behavior).getConstructor().newInstance(), in);
        return assertInstanceOf(Map.class, Codecs.encode(loader, out, answered));
    }

    private static Object field(Map<?, ?> out, String name) {
        return out.get(name);
    }
}
