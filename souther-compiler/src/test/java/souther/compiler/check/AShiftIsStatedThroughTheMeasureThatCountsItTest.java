package souther.compiler.check;

import souther.compiler.Compiler;
import souther.compiler.diag.Diagnostic;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * An operation that shifts a value by an amount states what it did through the measure that counts
 * the two apart: a date a day after another is a day after it, and that is the same number
 * {@code Date.daysBetween} answers. So a clause written in that measure reads the shift, and needs
 * no guard restating it.
 *
 * <p>A shift by an amount the measure does not fix says nothing: months and years hold different
 * numbers of days, so {@code Date.addMonths} moves a date by a count no rule here can write.
 */
class AShiftIsStatedThroughTheMeasureThatCountsItTest {

    private static List<String> codesOf(String module) {
        return Compiler.compileWithWarnings(module).warnings().stream()
                .map(Diagnostic::code)
                .toList();
    }

    private static final String TYPES = """
            module demo
            data Span = { from: Date, to: Date }
                invariant Date.daysBetween(from, to) >= 0
            data Window = { opens: DateTime, closes: DateTime }
                invariant DateTime.minutesBetween(opens, closes) >= 60
            """;

    @Test
    void aDateADayOnIsADayAfterTheOneItWasBuiltFrom() {
        assertEquals(List.of(), codesOf(TYPES + """
                behavior makeSpan : (d: Date) -> Span constructs Span
                let makeSpan (d) = Span { from = d, to = Date.addDays(1, d) }
                """));
    }

    @Test
    void anHourOnIsSixtyMinutesOn() {
        assertEquals(List.of(), codesOf(TYPES + """
                behavior makeWindow : (dt: DateTime) -> Window constructs Window
                let makeWindow (dt) = Window { opens = dt, closes = DateTime.addHours(1, dt) }
                """));
    }

    @Test
    void aMonthOnIsNoFixedNumberOfDays() {
        assertEquals(List.of("E2011"), codesOf(TYPES + """
                behavior makeSpan : (d: Date) -> Span constructs Span
                let makeSpan (d) = Span { from = d, to = Date.addMonths(1, d) }
                """));
    }
}
