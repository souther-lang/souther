package souther.compiler.partition;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The day of the month a date moved by months lands on is read in the cases the calendar tells
 * apart, as a line on the day of the date moved, and the cases are no lines of their own.
 * {@code AWeekdayOfADateMovedByMonthsIsReadToTheEndTest} reads the weekday through the same
 * cases, which costs more than a change waits for.
 */
class ADateMovedByMonthsIsReadWhereItsDaysAreKnownTest {

    private static final Map<String, Compilation> MEASURED = new ConcurrentHashMap<>();

    private static final String MODEL = """
            module demo

            behavior f : (x: Date, sunday: Date) -> Bool
            let f (x, sunday) = %s
            """;

    /** The day of the month a move lands on is a line on the day of the date moved. */
    @Test
    void theDayAMoveLandsOnIsALineOnTheDay() {
        List<BorderAssessment> lines = Adequacy.readingsOf(
                measured("Date.day(Date.addMonths(1, x)) >= 15").db(), "demo").get("f");
        assertEquals(List.of("Date.day(x)"), lines.stream().map(BorderAssessment::left).toList());
    }

    private static Compilation measured(String comparison) {
        return ACompiledModel.compiles(MEASURED.computeIfAbsent(MODEL.formatted(comparison),
                source -> {
                    Compilation compilation = Compilation.ofSource(source, "Main");
                    compilation.measure(Adequacy.Asked.fullReport());
                    return compilation;
                }));
    }

    /** And given back when the class is done with them: a fork keeps its JVM. */
    @AfterAll
    static void released() {
        MEASURED.clear();
    }
}
