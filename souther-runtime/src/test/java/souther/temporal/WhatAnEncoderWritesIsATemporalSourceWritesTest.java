package souther.temporal;

import java.time.Instant;
import java.time.LocalDate;
import java.time.LocalDateTime;
import java.time.LocalTime;
import java.util.List;
import java.util.Optional;
import java.util.Random;
import org.junit.jupiter.api.Test;
import souther.temporal.TemporalForms.Kind;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What an encoder writes for a value is a text source may write, which is inside what a boundary
 * reads.
 *
 * <p>Which text names a day and a moment that exist is the shared grammar's, held against
 * {@code java.time} where that grammar is. What is Souther's, and held here, is that holding a
 * {@code Time} to the second and writing an {@code Instant} in UTC leave out nothing a value is
 * written back as.
 */
class WhatAnEncoderWritesIsATemporalSourceWritesTest {

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
        assertEquals(Optional.empty(), TemporalForms.inSource(kind, text), kind + " in source: " + text);
        assertEquals(Optional.empty(), TemporalForms.atBoundary(kind, text), kind + " at a boundary: " + text);
    }
}
