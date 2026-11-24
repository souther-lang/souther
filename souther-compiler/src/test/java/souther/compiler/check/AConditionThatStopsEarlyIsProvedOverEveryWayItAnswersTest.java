package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.stdlib.Stdlib;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A body written with {@code &&} or {@code ||} is proved over every way it answers: the way the
 * right runs, and the way the left settles the answer without it.
 *
 * <p>The proofs read the right of such an operator under the left having let it run, so that a
 * site in it is asked only where a run reaches it. What the operator answers is another matter: on
 * the runs the left settles, it answers what the left came to, and a statement of the operation is
 * proved of those runs too. Held here with {@code List.isEmpty}, stated to be true exactly where
 * the list holds nothing, its body rewritten each way below: one that answers otherwise on some run
 * is refused, and one that answers so on every run is proved.
 */
class AConditionThatStopsEarlyIsProvedOverEveryWayItAnswersTest {

    private static final String IS_EMPTY_BODY = "List.length(xs) == 0";

    @Test
    void aBodyAnsweringOtherwiseWhereTheLeftSettlesItIsRefused() {
        for (String body : new String[] {"false && List.length(xs) == 0",
                "true || List.length(xs) == 0",
                "List.length(xs) > 0 && List.length(xs) == 0",
                "List.length(xs) > 0 || List.length(xs) == 0",
                "List.length(xs) == 0 && false",
                "List.length(xs) >= 0 || List.length(xs) == 0"}) {
            assertTrue(isEmptyIsLeftOpen(body), body);
        }
    }

    @Test
    void aBodyAnsweringSoOnEveryWayIsProved() {
        for (String body : new String[] {"List.length(xs) == 0 && true",
                "List.length(xs) == 0 || false",
                "List.length(xs) <= 0 && List.length(xs) == 0",
                "List.length(xs) == 0 || List.length(xs) < 0",
                "List.length(xs) > 0 && false || List.length(xs) == 0"}) {
            assertEquals(List.of(), unprovedOfIsEmpty(body), body);
        }
    }

    private static boolean isEmptyIsLeftOpen(String body) {
        return !unprovedOfIsEmpty(body).isEmpty();
    }

    /** What is stated of {@code List.isEmpty} that its body, rewritten to {@code body}, does not
     *  prove. */
    private static List<String> unprovedOfIsEmpty(String body) {
        BoundOperationFacts facts = OperationFactBinder.bindAll(rewritten(body));
        List<String> open = new ArrayList<>();
        facts.settled().forEach((operation, of) -> of.forEach((observed, settling) -> {
            if (operation.toString().contains("List.isEmpty")
                    && settling instanceof BoundOperationFacts.Settled.Open(var _, var why)) {
                open.add(observed + ": " + why);
            }
        }));
        facts.notProvedOfTheirBodies().forEach(each -> {
            if (each.toString().contains("List.isEmpty")) {
                open.add(each.toString());
            }
        });
        return open;
    }

    private static Stdlib rewritten(String body) {
        boolean[] changed = {false};
        Stdlib library = StdlibLoader.load(text -> {
            String out = text.replace("isEmpty (xs: List<'a>): Bool = " + IS_EMPTY_BODY,
                    "isEmpty (xs: List<'a>): Bool = " + body);
            changed[0] |= !out.equals(text);
            return out;
        });
        assertTrue(changed[0], "the rewrite matched nothing the library writes");
        return library;
    }
}
