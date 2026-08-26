package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.semantics.OperationFacts;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * The line a rule over one of these operations draws is at the numbers the operation was declared
 * with.
 *
 * <p>A border being drawn says the reading reached the form; it does not say the form is the right
 * one. {@code DateTime.addHours} declared to move a date-time by 360 seconds an hour draws a line
 * just as readily as one declared to move it by 3600, and a test asking only that a line is there
 * passes on both. What the coefficient is is the whole of what these declarations say — the values
 * are the carrier's units, and the carrier is not written down beside them — so it is what is read
 * here, off the label the border keeps.
 *
 * <p>Held to the declarations rather than to a list of its own. An operation declared to answer a
 * form of its arguments is an operation whose coefficients somebody chose, and a table written here
 * would cover the ones chosen today; this fails until the new one is measured, and the measurement
 * is where the next reader finds out what the numbers mean.
 */
class EveryDeclaredFormIsMeasuredAtItsOwnCoefficientsTest {

    /** A rule written over the operation, and the line it draws. */
    record Observation(String parameters, String condition, String label) {}

    /**
     * One rule per declared operation, and the line each draws.
     *
     * <p>Written as a rule and read as a line, so what is measured is what a model would get. The
     * unit is in the number: two minutes is 120 of the seconds a date-time counts, two hours 7200,
     * two days 172800, and a day put together out of a date and a time is 86400 of them.
     *
     * <p>Reachable from beside this rather than copied there. {@link
     * ARowComposedForAPointIsWritableAndStandsAtItTest} asks something else of the same models, and
     * a second table would be a second list of which operations there are — which is the one thing
     * the test above it exists to keep single.
     */
    static final Map<ValueName, Observation> MEASURED = measured();

    private static Map<ValueName, Observation> measured() {
        Map<ValueName, Observation> out = new LinkedHashMap<>();
        out.put(ValueName.Stdlib.operation("Decimal", "fromInt"),
                new Observation("a: Int, b: Decimal", "b > Decimal.fromInt(a)", "b = a"));
        out.put(ValueName.Stdlib.operation("Date", "daysBetween"),
                new Observation("a: Date, b: Date", "Date.daysBetween(a, b) > 10", "a = b - 10"));
        out.put(ValueName.Stdlib.operation("Date", "addDays"),
                new Observation("a: Date, b: Date", "b > Date.addDays(10, a)", "b = a + 10"));
        out.put(ValueName.Stdlib.operation("DateTime", "addMinutes"),
                new Observation("a: DateTime, b: DateTime", "b > DateTime.addMinutes(2, a)",
                        "b = a + 120"));
        out.put(ValueName.Stdlib.operation("DateTime", "addHours"),
                new Observation("a: DateTime, b: DateTime", "b > DateTime.addHours(2, a)",
                        "b = a + 7200"));
        out.put(ValueName.Stdlib.operation("DateTime", "addDays"),
                new Observation("a: DateTime, b: DateTime", "b > DateTime.addDays(2, a)",
                        "b = a + 172800"));
        out.put(ValueName.Stdlib.operation("DateTime", "fromDateAndTime"),
                new Observation("d: Date, t: Time, b: DateTime",
                        "b > DateTime.fromDateAndTime(d, t)", "b - 86400 * d - t = 0"));
        return out;
    }

    /** Every operation declared to answer a form of its arguments is measured here. */
    @Test
    void everyDeclaredFormIsMeasuredHere() {
        assertEquals(OperationFacts.answersAFormOfItsArguments(), MEASURED.keySet(),
                "an operation declared to answer a form of its arguments has its coefficients"
                        + " measured, and one measured here is one that is declared");
    }

    /** And each draws its line at the numbers it was declared with. */
    @Test
    void eachDrawsItsLineAtTheNumbersItWasDeclaredWith() {
        List<String> off = new ArrayList<>();
        MEASURED.forEach((operation, observed) -> {
            List<String> drawn = labelsOf(observed);
            if (!List.of(observed.label()).equals(drawn)) {
                off.add(operation + ": " + observed.condition() + " draws " + drawn
                        + " and not [" + observed.label() + "]");
            }
        });
        assertEquals(List.of(), off);
    }

    /**
     * The model one of these rules is measured in.
     *
     * <p>Beside the table rather than beside each reader of it. {@link
     * ARowComposedForAPointIsWritableAndStandsAtItTest} asks its own question of these same models,
     * and a second copy of this would be two models under one table — measured here and not there
     * the moment either copy moved.
     */
    static String modelOf(Observation observed) {
        return """
                module demo

                data Ok
                data No

                behavior f : (%s) -> Ok | No
                let f (%s) = {
                    guard %s else No
                    Ok
                }
                """.formatted(observed.parameters(),
                observed.parameters().replaceAll(":\\s*[A-Za-z<>]+", ""), observed.condition());
    }

    private static List<String> labelsOf(Observation observed) {
        String model = modelOf(observed);
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, PartitionEvidence> coverage =
                compilation.db().ask(new Adequacy.Coverage("demo")).value();
        assertNotNull(coverage, () -> "the model under test compiles: " + model);
        PartitionEvidence measured = coverage.get("f");
        assertNotNull(measured, () -> "f was measured: " + model);
        return measured.boundaries().stream().map(BorderAssessment::label).toList();
    }
}
