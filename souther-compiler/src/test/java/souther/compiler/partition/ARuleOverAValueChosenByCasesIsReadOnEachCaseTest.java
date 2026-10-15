package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A rule over a value chosen by cases is read on each case: where the case is taken, the rule is
 * the rule over what that case answers.
 *
 * <p>A body choosing between two constructions states a hundred thousand where {@code n > 0} and
 * two hundred thousand where not, so {@code n >= k.threshold} holds exactly where {@code n} is past
 * a hundred thousand: the second case is taken only where {@code n} is at most nought, where it is
 * never past two hundred thousand. Two lines, and nothing unread.
 *
 * <p>The same however the choice is spelled. Bound to a name and a field taken off it, chosen in a
 * helper the name is read through, or bound as a tuple and taken apart — what decides is the value
 * the arm answers, which is what the reading follows once it is on that arm. A reading that read
 * one arm's number for the position would state a hundred thousand of a model that says either;
 * this one states each, each where its case is taken.
 */
class ARuleOverAValueChosenByCasesIsReadOnEachCaseTest {

    /** The line the choice is made on, and the one the first case's threshold draws. */
    private static final String ON_EACH_CASE = "[n/x <= 0, n/0 < x < 100000, n/100000 <= x] unread []";

    @Test
    void eachCaseDrawsTheLineOfWhatItAnswers() {
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

        Map<String, String> onEachCase = new LinkedHashMap<>();
        read.keySet().forEach(spelling -> onEachCase.put(spelling, ON_EACH_CASE));
        assertEquals(onEachCase, read);
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
