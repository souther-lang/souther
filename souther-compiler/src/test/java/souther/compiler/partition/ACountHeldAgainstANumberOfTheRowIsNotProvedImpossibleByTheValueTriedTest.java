package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.RuleRequirement;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A count held against a number of the row is not proved impossible by the value the number was
 * first put at.
 *
 * <p>Which counts a statement like {@code count < on} leaves turns on where {@code on} stands, so a
 * count left nothing at one value of it says that value leaves none, and nothing about the rules.
 * Every shape here has rows on both sides — {@code on = 1} with nothing counted meets
 * {@code count < on} — and a search that put {@code on} at nought first and read the empty count
 * region as a proof reported the rule as one the rules leave no value for.
 *
 * <p>And counts held against numbers alone are still a proof where they leave nothing.
 */
class ACountHeldAgainstANumberOfTheRowIsNotProvedImpossibleByTheValueTriedTest {

    private static final String THE_INPUT = """
            module q

            data Yes
            data No
            data Answer = Yes | No

            behavior f : (on: Int, xs: List<Int>) -> Answer
            let f (on, xs) = if BODY then Yes else No
            """;

    private static final String COUNTED = "List.length(List.filter(x -> x <= 3, xs))";

    /** Shapes with a row on each side. */
    private static final List<String> SHAPES = List.of(
            "List.length(List.filter(x -> x <= on, xs)) >= on",
            COUNTED + " >= on",
            COUNTED + " == on",
            COUNTED + " > on",
            COUNTED + " + on < 2",
            COUNTED + " < on - 10",
            COUNTED + " >= on && on >= 5",
            COUNTED + " >= 2 && " + COUNTED + " < on");

    /**
     * No side of them is said to be one the rules leave no value for — asked apart from whether a
     * row was found, since a search that finds fewer rows is short and one that proves a side
     * empty is wrong.
     */
    @Test
    void noSideOfACountAgainstANumberOfTheRowIsProvedImpossible() {
        List<String> proved = new ArrayList<>();
        for (String shape : SHAPES) {
            List<String> kinds = kinds(shape);
            if (kinds.contains("NoValueCanTakeIt")) {
                proved.add(shape + ": " + kinds);
            }
        }

        assertEquals(List.of(), proved, "a side some row takes is not proved to be no row's");
    }

    /** And a row is found for each side, by putting the number where some count is left. */
    @Test
    void eachSideOfACountAgainstANumberOfTheRowIsComposed() {
        List<String> notComposed = new ArrayList<>();
        for (String shape : SHAPES) {
            List<String> kinds = kinds(shape);
            if (!kinds.equals(List.of("Required", "Required"))) {
                notComposed.add(shape + ": " + kinds);
            }
        }

        assertEquals(List.of(), notComposed,
                "a row on each side of a count held against a number of the row, which there is");
    }

    /** Proved of the way itself, which asks the one count to be two things before any value is
     *  put anywhere. */
    @Test
    void aCountAgainstANumberAloneThatLeavesNothingIsStillProved() {
        List<String> kinds = kinds(COUNTED + " >= 3 && " + COUNTED + " <= 1");
        assertEquals(1, kinds.stream().filter("OnePositionCannotBeBoth"::equals).count(),
                () -> "no count is at least three and at most one, which the counts settle by"
                        + " themselves: " + kinds);
    }

    private static List<String> kinds(String body) {
        Compilation compilation = Compilation.ofSource(THE_INPUT.replace("BODY", body), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String module = compilation.modules().getFirst();
        return compilation.db().ask(new Adequacy.DecisionSearch(module, "f")).value().values()
                .stream().map(each -> each.answer().settlement())
                .map(each -> each.requirement() instanceof RuleRequirement.Required
                        ? "Required" : each.requirement().getClass().getSimpleName())
                .sorted().toList();
    }
}
