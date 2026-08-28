package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A value written in a body is followed to wherever the number a rule compares against was written.
 *
 * <p>The seven spellings a rule can be written in are one line to a reader and one witness to this
 * compiler. What reads them is a relation rather than a list: an occurrence resolves through the
 * names the reading licenses and through the eliminations written against what those names hold,
 * and it does so as far as the writing goes. Crossing one construction and stopping reads all seven
 * of them, so nothing in the seven says which of the two was built.
 *
 * <p>These say it. A construction inside a construction and a name given the value halfway are two
 * spellings a single crossing does not reach; a helper's parameter is what says the value is
 * followed under the environment the construction was written in and not under the one the
 * projection was; a number wrapped in arithmetic is what says the wrapping is taken off by this
 * grammar rather than recognised by a carrier as a value written out.
 *
 * <p>A tuple is here for the same reason and not as a second feature. This language writes no
 * projection of one — a {@code let (a, b) = t} is where {@code Core.TupleGet} comes from — and
 * taking the element a tuple was written with is the elimination a construction's field already is.
 * Read one and not the other, the relation would hold of whichever constructor a reader happened to
 * meet.
 */
class AConstructionIsFollowedWhereverTheValueItBuiltStandsTest {

    private static final String LINE = "[n/x < 100000, n/100000 <= x] unread []";

    @Test
    void aValueIsFollowedThroughEveryProjectionWrittenAgainstIt() {
        Map<String, String> read = new LinkedHashMap<>();
        read.put("aConstructionInsideAConstruction", reading(
                "if n >= Outer { big = Big { threshold = 100000 } }.big.threshold"
                        + " then Yes else No"));
        read.put("aNameGivenTheValueHalfway", reading("""
                {
                        let outer = Outer { big = Big { threshold = 100000 } }
                        let big = outer.big
                        if n >= big.threshold then Yes else No
                    }"""));
        read.put("aFieldGivenAName", reading("""
                {
                        let inner = Big { threshold = 100000 }
                        if n >= Outer { big = inner }.big.threshold then Yes else No
                    }"""));
        read.put("aHelpersParameter", reading("if n >= bigOf(100000).threshold then Yes else No"));
        read.put("aHelpersParameterInsideAConstruction",
                reading("if n >= outerOf(100000).big.threshold then Yes else No"));
        read.put("aNewtypeOverArithmetic", reading("""
                {
                        let y = Yen(99999 + 1)
                        if n >= y.value then Yes else No
                    }"""));
        read.put("aTuplesElement", reading("""
                {
                        let (a, b) = (100000, 1)
                        if n >= a then Yes else No
                    }"""));
        read.put("aTupleGivenAName", reading("""
                {
                        let t = (100000, 1)
                        let (a, b) = t
                        if n >= a then Yes else No
                    }"""));
        read.put("aConstructionInsideATuple", reading("""
                {
                        let (a, b) = (Big { threshold = 100000 }, 1)
                        if n >= a.threshold then Yes else No
                    }"""));

        Map<String, String> oneLineEach = new LinkedHashMap<>();
        read.keySet().forEach(spelling -> oneLineEach.put(spelling, LINE));
        assertEquals(oneLineEach, read);
    }

    private static String reading(String body) {
        return MeasuredBehavior.reading("""
                module g

                data Big = { threshold: Int }
                data Outer = { big: Big }
                data Yen = Int
                data Yes
                data No

                let bigOf (t: Int) = Big { threshold = t }
                let outerOf (t: Int) = Outer { big = Big { threshold = t } }

                behavior classify : (n: Int) -> Yes | No
                let classify (n) = %s

                example classify
                    | "one" : (1) -> No
                """.formatted(body), "classify");
    }
}
