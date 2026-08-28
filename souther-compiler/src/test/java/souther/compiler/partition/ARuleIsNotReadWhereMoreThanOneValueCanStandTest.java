package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static souther.compiler.partition.ARuleReachedThroughAConstructedValueIsReadTest.reading;

/**
 * Where more than one value can stand at a position, no rule is read off any of them.
 *
 * <p>What a measure answers is what the model states about every value that can stand where the
 * rule is written. A body that chooses between two constructions states no number at the position
 * the choice stands at, and a reading that followed one arm would answer a hundred thousand for a
 * model that says a hundred thousand or two hundred thousand — a rule about a value, reported as a
 * rule about the model.
 *
 * <p>Nothing here refuses anything. What holds these open is that the relation which follows a
 * value has no rule for a choice and none for an element: it takes an elimination against the
 * introduction written for it, and neither an arm nor a list element is one. So there is no list of
 * shapes to keep in step with the shapes that do read, and a construction that becomes readable
 * does not quietly make these readable with it.
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

    /**
     * And an element of a written list answers for none of them either.
     *
     * <p>Its own claim beside the three above. A choice is written where the value stands and a
     * list element is not: what names the element is a binding an operation handed it, and what
     * holds this open is that such a name is not one the reading says stands for a single value.
     * The two boundaries are kept by different answers and are stated apart.
     */
    @Test
    void anElementOfAWrittenListAnswersForNoneOfThem() {
        assertEquals("[] unread [n UNSUPPORTED_SYNTAX]", reading("""
                {
                        let ks = [ Big { threshold = 100000 }, Big { threshold = 200000 } ]
                        if List.any((k) -> n >= k.threshold, ks) then Yes else No
                    }"""));
    }

    /**
     * And a case bound off one is still an element, however narrowly the arm names it.
     *
     * <p>An arm that admits one case looks as though it says which element is standing there, and
     * it does not: a list may be written with two of the same case, and each of them would satisfy
     * the arm with a different number under it. So the number a rule compares against is reached
     * here through a name whose value the reading does not single out, and the arm is no part of
     * whether it does.
     *
     * <p>This is the shape a model reaches it by, which is why it is written out rather than left
     * to the two above. Narrowing an element to a case is where a reader would expect the value to
     * become one, and it is exactly where nothing has said so.
     */
    @Test
    void andACaseBoundOffAnElementIsStillOne() {
        assertEquals("[] unread [n UNSUPPORTED_SYNTAX]", reading("""
                {
                        let ks = [ AtMost { threshold = 100000 }, Whatever ]
                        if List.any((k) -> reaches(n, k), ks) then Yes else No
                    }"""));
    }
}
