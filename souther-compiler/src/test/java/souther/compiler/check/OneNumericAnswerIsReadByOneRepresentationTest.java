package souther.compiler.check;

import souther.compiler.DefaultStdlib;
import souther.compiler.semantics.OperationFacts;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The number an operation answers is read by one representation.
 *
 * <p>A term standing for a call, the form its result is of its arguments, the arithmetic it
 * computes, the body the language writes out — each is an account of the same number, and two of
 * them at one call is not two opinions but a report whose content depends on which reader arrived.
 * {@code Decimal.fromInt(n)} declared as a term as well as a form would be {@code n} to a check
 * reading forms and an opaque number to a check reading terms.
 *
 * <p>Held of every operation the library declares and not of the ones some question asks about. The
 * exclusivity is a property of the declarations, so a range that moved would move what is exclusive
 * with it — and the operations no question asks about today are exactly the ones nobody would think
 * to check by hand.
 *
 * <p>{@code None} is not a failure here. Most of what the library answers is read by nothing, which
 * is ordinary; where a reading is owed it is a question's range that says so, and that is asked in
 * {@code AnOperationTheLibraryGainsIsAnsweredForTest}.
 */
class OneNumericAnswerIsReadByOneRepresentationTest {

    @Test
    void noOperationsNumberIsReadByTwoRepresentations() {
        List<String> twice = new ArrayList<>();
        for (Map.Entry<String, Stdlib.Entry> e : DefaultStdlib.get().entries().entrySet()) {
            ValueName operation = DefaultStdlib.get().operation(e.getKey());
            if (NumericReadings.resolve(DefaultStdlib.get(), OperationFacts.declarations(),
                    operation) instanceof NumericReadings.Resolution.Multiple(List<NumericReading> readings)) {
                twice.add(e.getKey() + " — " + String.join(" and ",
                        readings.stream().map(NumericReading::describes).toList()));
            }
        }
        assertEquals(List.of(), twice,
                "the number each of these answers is read by more than one representation, so which"
                        + " reading a report shows is whichever reader arrived");
    }

    /**
     * An operation that answers no number has no reading of one.
     *
     * <p>{@code Date.addDays} declares a form and answers a date. The form is about what its
     * arguments are counted as, which is what lets a date take part in one at all; it is not an
     * account of a number the operation answered, because it answered none. Counted as one, every
     * such operation would carry a reading whose subject is missing — and a proposition with no
     * subject cannot come out false, so the count would look right for the wrong reason.
     */
    @Test
    void anOperationThatAnswersNoNumberIsReadByNothing() {
        assertEquals(new NumericReadings.Resolution.None(),
                NumericReadings.resolve(DefaultStdlib.get(), OperationFacts.declarations(),
                        DefaultStdlib.get().operation("Date.addDays")),
                "a form over what its arguments are counted as is not a reading of a number this"
                        + " operation answers, since it answers a date");
    }
}
