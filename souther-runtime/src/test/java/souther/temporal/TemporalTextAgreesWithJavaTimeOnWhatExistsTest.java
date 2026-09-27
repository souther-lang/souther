package souther.temporal;

import java.time.DateTimeException;
import java.time.Instant;
import java.time.LocalDate;
import java.time.LocalDateTime;
import java.time.LocalTime;
import java.time.format.DateTimeFormatter;
import java.util.List;
import java.util.Optional;
import java.util.Random;
import java.util.function.Supplier;
import org.junit.jupiter.api.Test;
import souther.temporal.TemporalText.Kind;
import souther.temporal.TemporalText.Refusal;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What {@link TemporalText} says exists is what {@code java.time} can hold, and what an encoder
 * writes is inside what source writes, which is inside what a boundary reads.
 *
 * <p>The grammar is a regular expression and what exists is arithmetic on the fields, so
 * {@code java.time} decides nothing there. It is the oracle here: a value it can build from a text
 * that is in the form is a value this must admit, and one it refuses this must refuse, at the ends
 * of every range as much as in the middle. The ends are where a domain borrowed from another type
 * shows itself: an {@code Instant} reaches a year past a {@code LocalDate} on either side, and a
 * moment written near the end that an offset or an hour 24 carries over it is the case that has to
 * come out the way the value it names does.
 */
class TemporalTextAgreesWithJavaTimeOnWhatExistsTest {

    private static final long[] YEAR_EDGES = {
            0, 1, -1, 4, 100, 400, 1900, 2000, 2026, 2028, 9999, 10000, -9999, -10000,
            999_999_998, 999_999_999, 1_000_000_000, 1_000_000_001,
            -999_999_998, -999_999_999, -1_000_000_000, -1_000_000_001};

    /** A year as the grammar spells it: no sign for 0000 to 9999, otherwise a sign and no padding. */
    private static String year(long year) {
        if (year >= 0 && year <= 9999) {
            return "%04d".formatted(year);
        }
        if (year < 0 && year >= -9999) {
            return "-%04d".formatted(-year);
        }
        return (year > 0 ? "+" : "-") + Math.abs(year);
    }

    private static boolean builds(Supplier<Object> value) {
        try {
            return value.get() != null;
        } catch (DateTimeException _) {
            return false;
        }
    }

    private static boolean localDateExists(long year, int month, int day) {
        return Math.abs(year) <= 999_999_999L && builds(() -> LocalDate.of((int) year, month, day));
    }

    private static boolean localTimeExists(int hour, int minute, int second) {
        return builds(() -> LocalTime.of(hour, minute, second));
    }

    /** Every day a year at either end of the range and a leap year can be given, in and out of it. */
    @Test
    void aDateExistsWhereALocalDateHolds() {
        for (long year : YEAR_EDGES) {
            for (int month = 0; month <= 13; month++) {
                for (int day = 0; day <= 32; day++) {
                    String text = year(year) + "-%02d-%02d".formatted(month, day);
                    assertEquals(localDateExists(year, month, day),
                            TemporalText.atBoundary(Kind.DATE, text).isEmpty(), text);
                }
            }
        }
    }

    @Test
    void aTimeOfDayExistsWhereALocalTimeHolds() {
        for (int hour = 0; hour <= 25; hour++) {
            for (int minute = 0; minute <= 61; minute++) {
                String text = "%02d:%02d".formatted(hour, minute);
                assertEquals(localTimeExists(hour, minute, 0),
                        TemporalText.atBoundary(Kind.TIME, text).isEmpty(), text);
                for (int second = 0; second <= 61; second += second < 58 ? 19 : 1) {
                    String withSeconds = text + ":%02d".formatted(second);
                    assertEquals(localTimeExists(hour, minute, second),
                            TemporalText.atBoundary(Kind.TIME, withSeconds).isEmpty(), withSeconds);
                }
            }
        }
    }

    /**
     * A moment exists where an {@code Instant} holds it, whichever of its fields carries it there:
     * a year at the end, an hour 24, an offset. Fields are drawn at random from the ends of every
     * one of them, and the same seed draws the same texts.
     */
    @Test
    void aMomentExistsWhereAnInstantHoldsIt() {
        Random random = new Random(2007);
        int[] offsetHours = {0, 1, 9, 17, 18, 19, 23};
        int admitted = 0;
        int refused = 0;
        for (int i = 0; i < 200_000; i++) {
            long year = random.nextInt(4) == 0
                    ? YEAR_EDGES[random.nextInt(YEAR_EDGES.length)]
                    : random.nextLong(-1_000_000_003L, 1_000_000_004L);
            int hour = random.nextInt(5) == 0 ? 24 : random.nextInt(24);
            int minute = hour == 24 && random.nextInt(8) != 0 ? 0 : random.nextInt(60);
            int second = hour == 24 && random.nextInt(8) != 0 ? 0 : random.nextInt(60);
            String fraction = random.nextInt(6) == 0 ? "." + "123456789".substring(0, 1 + random.nextInt(9)) : "";
            String offset = random.nextInt(3) == 0 ? "Z"
                    : (random.nextBoolean() ? "+" : "-")
                            + "%02d:%02d".formatted(offsetHours[random.nextInt(offsetHours.length)],
                                    random.nextInt(60))
                            + (random.nextInt(4) == 0 ? ":%02d".formatted(random.nextInt(60)) : "");
            String text = year(year) + "-%02d-%02dT%02d:%02d:%02d%s%s".formatted(
                    1 + random.nextInt(random.nextInt(9) == 0 ? 14 : 12),
                    1 + random.nextInt(random.nextInt(9) == 0 ? 33 : 28),
                    hour, minute, second, fraction, offset);

            boolean held = builds(() -> Instant.from(DateTimeFormatter.ISO_INSTANT.parse(text)));
            assertEquals(held, TemporalText.atBoundary(Kind.INSTANT, text).isEmpty(), text);
            if (held) {
                admitted++;
            } else {
                refused++;
            }
        }
        assertTrue(admitted > 20_000 && refused > 20_000,
                "the draw has to reach both answers to say anything: " + admitted + " and " + refused);
    }

    /** The two ends of what an {@code Instant} holds, and the moments a carry puts one past them. */
    @Test
    void anInstantsRangeEndsWhereAnInstantsDoes() {
        assertEquals(Optional.empty(), TemporalText.atBoundary(Kind.INSTANT, Instant.MIN.toString()));
        assertEquals(Optional.empty(), TemporalText.atBoundary(Kind.INSTANT, Instant.MAX.toString()));
        for (String past : List.of(
                "-1000000001-12-31T23:59:59Z", "+1000000001-01-01T00:00:00Z",
                "+1000000000-12-31T24:00:00Z", "-1000000000-01-01T00:00:00+01:00",
                "+1000000000-12-31T23:59:59-00:00:01")) {
            assertEquals(Optional.of(Refusal.MALFORMED), TemporalText.atBoundary(Kind.INSTANT, past), past);
        }
        for (String carried : List.of(
                "+999999999-12-31T24:00:00Z", "-999999999-01-01T00:00:00+18:00",
                "+1000000000-12-31T23:59:59.999999999Z", "-1000000000-01-01T00:00:00-00:00:00")) {
            assertEquals(Optional.empty(), TemporalText.atBoundary(Kind.INSTANT, carried), carried);
        }
    }

    /** What an encoder writes for a value is a text a boundary reads, and source may write it. */
    @Test
    void whatAnEncoderWritesIsWhatSourceWritesAndABoundaryReads() {
        Random random = new Random(2026);
        for (int i = 0; i < 50_000; i++) {
            Instant moment = Instant.ofEpochSecond(
                    random.nextLong(Instant.MIN.getEpochSecond(), Instant.MAX.getEpochSecond() + 1),
                    random.nextInt(3) == 0 ? random.nextInt(1_000_000_000) : 0);
            assertWritten(Kind.INSTANT, moment.toString());
            LocalDate date = LocalDate.ofEpochDay(random.nextLong(LocalDate.MIN.toEpochDay(),
                    LocalDate.MAX.toEpochDay() + 1));
            assertWritten(Kind.DATE, date.toString());
            LocalTime time = LocalTime.ofSecondOfDay(random.nextInt(86_400));
            assertWritten(Kind.TIME, time.toString());
            assertWritten(Kind.DATETIME, LocalDateTime.of(date, time).toString());
        }
        for (Instant edge : List.of(Instant.MIN, Instant.MAX, Instant.EPOCH,
                Instant.MIN.plusNanos(1), Instant.MAX.minusNanos(1))) {
            assertWritten(Kind.INSTANT, edge.toString());
        }
        assertWritten(Kind.DATE, LocalDate.MIN.toString());
        assertWritten(Kind.DATE, LocalDate.MAX.toString());
        assertWritten(Kind.DATETIME, LocalDateTime.of(LocalDate.MIN, LocalTime.MIDNIGHT).toString());
        assertWritten(Kind.DATETIME, LocalDateTime.of(LocalDate.MAX, LocalTime.of(23, 59, 59)).toString());
        assertWritten(Kind.TIME, LocalTime.MIDNIGHT.toString());
        assertWritten(Kind.TIME, LocalTime.of(23, 59, 59).toString());
    }

    private static void assertWritten(Kind kind, String text) {
        assertEquals(Optional.empty(), TemporalText.inSource(kind, text), kind + " in source: " + text);
        assertEquals(Optional.empty(), TemporalText.atBoundary(kind, text), kind + " at a boundary: " + text);
    }
}
