package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.meaning.WhyNotTaken;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.RuleRequirement;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What some or every element is asked, taken apart into the ways an element may meet it, leaves
 * out the ways no element meets, and stops where the ones left are more than are read.
 *
 * <p>A conjunction of choices over one number is, taken apart, as many ways as the choices
 * multiplied, and nearly all of them ask an element to be at most one number and at least a larger
 * one. Those are proved closed by what the declarations leave and not looked at again, so what is
 * left is few. Where the choices are over things that do not exclude each other every way is open,
 * and past the figure the statement is said to be where this compiler's work stopped — not unread,
 * and not something a row has no words for.
 */
class TheWaysAnElementMayMeetAStatementLeaveOutTheOnesNoElementMeetsTest {

    private static final String THE_INPUT = """
            module q

            data Yes
            data No
            data Answer = Yes | No

            behavior f : (on: Int, xs: List<Int>) -> Answer
            let f (on, xs) = if BODY then Yes else No
            """;

    @Test
    void choicesNoElementMeetsTogetherAreLeftOutAndTheRestComposed() {
        List<String> parts = new ArrayList<>();
        for (int each = 0; each < 20; each++) {
            parts.add("(x <= " + each + " || x >= " + (100 + each) + ")");
        }
        Compilation compilation = compiled(
                "List.any(x -> " + String.join(" && ", parts) + ", xs)");
        String module = compilation.modules().getFirst();

        assertEquals(List.of(true, true), compilation.db()
                        .ask(new Adequacy.DecisionSearch(module, "f")).value().values().stream()
                        .map(each -> each.settlement().requirement()
                                instanceof RuleRequirement.Required)
                        .toList(),
                "a row for each rule");
    }

    /**
     * Choices every way of which some element meets, more of them than are read: the ways read are
     * kept and the rest are said to be where the figure stopped — beside them on the way, so a row
     * is composed along the ones read and a way past them is not taken to be closed.
     */
    @Test
    void choicesAnElementMeetsInEveryWayKeepWhatWasReadAndSayTheRestStopped() {
        String source = PAIRS.replace("BODY", "List.any(x -> " + pastTheFigure() + ", xs)");

        boolean said = false;
        for (DecisionReading.Ruled each : DecisionReadings.of(source, "f").found()) {
            said |= each.states().declined().stream().anyMatch(declined -> declined.whys()
                    .contains(new WhyNotTaken.MoreWaysThanAreRead()));
        }
        assertTrue(said, "the ways past the figure are said to be where this compiler stopped");

        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String module = compilation.modules().getFirst();
        assertEquals(List.of(true, true), compilation.db()
                        .ask(new Adequacy.DecisionSearch(module, "f")).value().values().stream()
                        .map(each -> each.settlement().requirement()
                                instanceof RuleRequirement.Required)
                        .toList(),
                "and a row for each rule along the ways that were read");
    }

    /** Elements of two numbers, so a conjunction of choices between them has a way for every
     *  choice of each and none is closed by another. */
    private static final String PAIRS = """
            module q

            data P = { a: Int, b: Int }
            data Yes
            data No
            data Answer = Yes | No

            behavior f : (xs: List<P>) -> Answer
            let f (xs) = if BODY then Yes else No
            """;

    /**
     * Some element meeting one of two things, one of which comes to more ways than are read, is
     * found along the other or along the ways of the first that were read — whichever is written
     * first. A figure that stops one alternative leaves the rest of the choice as it was.
     */
    @Test
    void aChoiceOneSideOfWhichPassesTheFigureIsComposedAlongWhatWasRead() {
        String past = pastTheFigure();
        for (String body : List.of("x.a == 357 || " + past, past + " || x.a == 357")) {
            Compilation compilation = Compilation.ofSource(
                    PAIRS.replace("BODY", "List.any(x -> " + body + ", xs)"), "Main");
            compilation.measure(Adequacy.Asked.fullReport());
            compilation.answerEverything();
            String module = compilation.modules().getFirst();

            assertEquals(List.of(true, true), compilation.db()
                            .ask(new Adequacy.DecisionSearch(module, "f")).value().values()
                            .stream()
                            .map(each -> each.settlement().requirement()
                                    instanceof RuleRequirement.Required)
                            .toList(),
                    () -> "a row for each rule of " + body);
        }
    }

    /** A conjunction of choices between the two numbers of an element, every way of which an
     *  element meets, and more of them than a reading of one condition makes. */
    static String pastTheFigure() {
        List<String> parts = new ArrayList<>();
        for (int each = 0; each < 10; each++) {
            parts.add("(x.a >= " + (10 + each) + " || x.b >= " + (10 + each) + ")");
        }
        return "(" + String.join(" && ", parts) + ")";
    }

    private static Compilation compiled(String body) {
        Compilation compilation = Compilation.ofSource(THE_INPUT.replace("BODY", body), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }
}
