package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A number a rule compares against is read where it is reached through a value the body constructs.
 *
 * <p>One line at a hundred thousand, written seven ways. A number written out was read and the same
 * number reached through a construction was not, and the position it divides got no axis at all —
 * so a model stating where its values part was reported as stating nothing there, over a difference
 * in how the number was spelled.
 *
 * <p>A name in the middle is no part of it either way, which is why the two spellings that already
 * read are held here beside the five that did not. What stops a reading is what the number came
 * through and not the binding it was given, and a change that gains the five by losing either of
 * those two has not read one rule seven ways.
 */
class ARuleReachedThroughAConstructedValueIsReadTest {

    private static final String LINE = "[n/x < 100000, n/100000 <= x] unread []";

    @Test
    void oneLineIsReadHoweverTheNumberIsReached() {
        Map<String, String> read = new LinkedHashMap<>();
        read.put("written", reading("if n >= 100000 then Yes else No"));
        read.put("namedNumber", reading("""
                {
                        let t = 100000
                        if n >= t then Yes else No
                    }"""));
        read.put("constructionInPlace",
                reading("if n >= Big { threshold = 100000 }.threshold then Yes else No"));
        read.put("namedConstruction", reading("""
                {
                        let k = Big { threshold = 100000 }
                        if n >= k.threshold then Yes else No
                    }"""));
        read.put("namedField", reading("""
                {
                        let t = Big { threshold = 100000 }.threshold
                        if n >= t then Yes else No
                    }"""));
        read.put("newtypeProjection", reading("""
                {
                        let y = Yen(100000)
                        if n >= y.value then Yes else No
                    }"""));
        read.put("throughAHelper", reading("if n >= bigOne(n).threshold then Yes else No"));

        Map<String, String> oneLineEach = new LinkedHashMap<>();
        read.keySet().forEach(spelling -> oneLineEach.put(spelling, LINE));
        assertEquals(oneLineEach, read);
    }

    /** What the measure made of a behavior whose body is {@code body}: its classes, and what it
     *  could not read. */
    static String reading(String body) {
        String source = """
                module g

                data Big = { threshold: Int }
                data Outer = { big: Big }
                data Yen = Int
                data Yes
                data No

                data AtMost = { threshold: Int }
                data Whatever
                data Reason = AtMost | Whatever

                let reaches (n: Int, reason: Reason): Bool =
                    match reason with
                        | AtMost { threshold } -> n >= threshold
                        | Whatever             -> true

                let bigOne (n: Int) = Big { threshold = 100000 }
                let bigOf (t: Int) = Big { threshold = t }
                let outerOf (t: Int) = Outer { big = Big { threshold = t } }
                let chooseBig (c: Bool) =
                    if c then Big { threshold = 100000 } else Big { threshold = 200000 }

                behavior classify : (n: Int) -> Yes | No
                let classify (n) = %s

                example classify
                    | "one" : (1) -> No
                """.formatted(body);
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        AdequacyReport.BehaviorReport behavior = AdequacyReport.of(compilation)
                .modules().get(0).behaviors().stream()
                .filter(each -> each.name().equals("classify")).findFirst().orElseThrow();
        return "[" + behavior.partition().axes().stream()
                .flatMap(axis -> axis.classes().stream())
                .collect(Collectors.joining(", "))
                + "] unread [" + behavior.partition().notRead().stream()
                .map(each -> each.at() + " " + each.reason())
                .collect(Collectors.joining(", ")) + "]";
    }
}
