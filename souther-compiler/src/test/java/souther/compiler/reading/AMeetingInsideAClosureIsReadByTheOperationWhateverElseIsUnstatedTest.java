package souther.compiler.reading;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static souther.compiler.reading.ReadInteractions.readAll;

/**
 * The body of a function value belongs to the operation it is handed to, which reads what the body
 * decides. That does not turn on what else could not be stated of the way to it: a closure under the
 * arm of an attempt is the closure of the same operation, and the meeting in it is said once.
 */
class AMeetingInsideAClosureIsReadByTheOperationWhateverElseIsUnstatedTest {

    private static final String MODEL = """
            module example.closure

            data Row = { active: Bool }
            data Small = { n: Int }
                invariant n >= 0

            behavior total : (first: Row, flag: Bool, a: Int) -> Int

            let total (first, flag, a) =
                %s
            """;

    private static final String CHOICES = "(if r.active then 1 else 0) + (if flag then 1 else 0)";

    @Test
    void theMeetingInTheClosureIsSaidOnceWhereverTheClosureIsWritten() {
        List<WhyNotJoined> alone = readAll(MODEL.formatted(
                "List.sum(List.map(r -> " + CHOICES + ", [ first ]))"), "total").notJoined();
        List<WhyNotJoined> underAnAttempt = readAll(MODEL.formatted(
                "if Small { n = a } as small\n"
                        + "    then List.sum(List.map(r -> " + CHOICES + ", [ first ]))\n"
                        + "    else 0"), "total").notJoined();

        assertEquals(List.of(WhyNotJoined.A_VALUE_CHOICE_NOT_READ), alone,
                "the operation says what it did not read");
        assertEquals(alone, underAnAttempt,
                "and says the same under the arm of an attempt, and no more");
    }
}
