package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Where more than one value can stand at a position, no rule is read off any of them.
 *
 * <p>What a measure answers is what the model states about every value that can stand where the
 * rule is written. A body that chooses between two constructions states no number at the position
 * the choice stands at, and a reading that followed one arm would answer a hundred thousand for a
 * model that says a hundred thousand or two hundred thousand — a rule about a value, reported as a
 * rule about the model.
 *
 * <p>Nothing here refuses anything. What holds these open is that the reading names no values for
 * what stands at a choice: the relation which follows a value takes an elimination against the
 * introduction written for it and a name the reading answers for, and an arm of a choice is
 * neither. So there is no list of shapes to keep in step with the shapes that do read, and a
 * construction that becomes readable does not quietly make these readable with it.
 *
 * <p>Which is a different boundary from the one a container has, and it is why an element of a
 * written list is not here. That one is a name the reading can write out every value of, and what a
 * rule over it comes to is what those values agree on
 * ({@link ARuleAboutAnElementIsReadWhereTheyAllSupportOneFormTest}). A choice has no such answer
 * and gets none from anywhere.
 *
 * <p>The helper is the stronger of the two alternatives. The name it was given is read through, so
 * the reading is inside the helper's body when it meets the choice — which is where a relation that
 * stopped at names rather than at what they hold would already have answered.
 *
 * <p>Each of these is reported as a rule written in a form this compiler does not read, which is
 * the word such a position already had. A position holding a choice is not a new kind of thing to
 * tell a reader about.
 */
class ARuleIsNotReadWhereMoreThanOneValueCanStandTest {

    /** The `n > 0` the choice is made on is a line of its own, and it is the only one. */
    private static final String ONLY_THE_CHOICE =
            "[n/x <= 0, n/0 < x] unread [n UNSUPPORTED_SYNTAX]";

    @Test
    void neitherArmAnswersForThePositionTheChoiceStandsAt() {
        Map<String, String> read = new LinkedHashMap<>();
        read.put("betweenTwoConstructions", reading("""
                {
                        let k = if n > 0 then Big { threshold = 100000 }
                                else Big { threshold = 200000 }
                        if n >= k.threshold then Yes else No
                    }"""));
        read.put("fromAHelperThatChooses",
                reading("if n >= chooseBig(n > 0).threshold then Yes else No"));
        read.put("betweenTwoTuples", reading("""
                {
                        let (a, b) = if n > 0 then (100000, 1) else (200000, 1)
                        if n >= a then Yes else No
                    }"""));

        Map<String, String> nothingButTheChoice = new LinkedHashMap<>();
        read.keySet().forEach(spelling -> nothingButTheChoice.put(spelling, ONLY_THE_CHOICE));
        assertEquals(nothingButTheChoice, read);
    }

    private static String reading(String body) {
        return MeasuredBehavior.reading("""
                module g

                data Big = { threshold: Int }
                data Yes
                data No

                let chooseBig (c: Bool) =
                    if c then Big { threshold = 100000 } else Big { threshold = 200000 }

                behavior classify : (n: Int) -> Yes | No
                let classify (n) = %s

                example classify
                    | "one" : (1) -> No
                """.formatted(body), "classify");
    }
}
