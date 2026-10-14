package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.RuleRequirement;
import souther.compiler.query.SettledAt;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What an operation means of a list does not turn on where the list stands.
 *
 * <p>The same condition over a list the input holds and over one a dependency answered is searched
 * for a row of each rule of the way, and each rule comes to the same: a row a run was seen to take
 * it with, or a row composed short of what the way asks. A shape one of them reads and the other
 * does not is a meaning written twice — which is what made a filter over an answer unread, and what
 * this holds the two to.
 *
 * <p>Only the shapes the two agree on. A shape they part on is a limit of one of them that is not a
 * rule of the language, and holding it here would hold the limit.
 */
class TheSameStatementIsComposedWhereverTheListStandsTest {

    private static final String AN_ANSWER = """
            module p

            data Cat = A | B
            data Sched = List<Int>
            data Yes
            data No
            data Answer = Yes | No

            behavior sched1 : (c: Cat) -> Sched

            behavior f : (c: Cat, on: Int) -> Answer
                depends on sched1
            let f (c, on, sched1) = if BODY then Yes else No
            """;

    private static final String THE_INPUT = """
            module q

            data Yes
            data No
            data Answer = Yes | No

            behavior f : (on: Int, xs: List<Int>) -> Answer
            let f (on, xs) = if BODY then Yes else No
            """;

    @Test
    void everyShapeIsSearchedTheSameWhereverItsListStands() {
        List<String> shapes = List.of(
                "List.any(x -> x <= on, LIST) || List.any(x -> x > 3, LIST)",
                "Bool.not(List.any(x -> x <= on, LIST))",
                "List.all(x -> x <= on, LIST)",
                "List.length(List.filter(x -> x <= on, LIST)) == 0",
                "List.length(List.filter(x -> x <= on, LIST)) >= on",
                "List.length(List.filter(x -> x <= 3, LIST)) < on",
                "List.any(x -> x <= 3, List.filter(y -> y > on, LIST))",
                "List.any(x -> x <= 3, List.reverse(LIST))",
                "List.isEmpty(LIST)",
                "List.length(LIST) + on >= 3",
                "List.length(LIST) * on >= 3",
                "List.length(List.distinct(LIST)) >= on",
                "List.any(x -> x == on, LIST)",
                "List.length(LIST) >= 1 && List.length(LIST) <= on",
                "List.any(x -> x <= on, LIST) && List.any(x -> x > on, LIST)",
                "List.length(List.map(x -> x + on, LIST)) >= 2",
                "List.any(x -> x <= on, List.map(y -> y + on, LIST))");
        List<String> parted = new ArrayList<>();
        boolean someRowWasFound = false;
        for (String shape : shapes) {
            List<String> fromAnswer = kinds(AN_ANSWER, shape.replace("LIST", "sched1(c).value"));
            List<String> fromInput = kinds(THE_INPUT, shape.replace("LIST", "xs"));
            if (!fromAnswer.equals(fromInput)) {
                parted.add(shape + ": " + fromAnswer + " against " + fromInput);
            }
            someRowWasFound |= fromAnswer.contains("Required");
        }

        assertEquals(List.of(), parted,
                "a shape searched one way where the list is an answer and another where it is an"
                        + " input is an operation read twice");
        assertTrue(someRowWasFound, "and the shapes held to each other are ones a row was found for");
    }

    /** What the search came to for each rule of the way, in an order that is no rule's. */
    private static List<String> kinds(String model, String body) {
        Compilation compilation = Compilation.ofSource(model.replace("BODY", body), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String module = compilation.modules().getFirst();
        return compilation.db().ask(new Adequacy.DecisionSearch(module, "f")).value().values()
                .stream().map(SettledAt::settlement)
                .map(each -> each.requirement() instanceof RuleRequirement.Required
                        ? "Required" : each.requirement().getClass().getSimpleName())
                .sorted().toList();
    }
}
