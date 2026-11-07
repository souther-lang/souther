package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the format of a string shows of a remainder of its code points is asked under the steps a
 * search may take, shared out among the questions asked: one share for each code point of the
 * dividend and one for the form, and inside a question again among the sets of code points the
 * format takes apart at the places held still. A question that runs out says the share it was
 * compared against, and a divisor past the whole figure says the whole figure.
 *
 * <p>Each held by a model reaching that stop and by the report it is told in: eleven digits
 * weighed and divided, and code points beside the remainder that a format takes apart into ten
 * sets each — a digit, then the letter that digit is written with. The share is worked out here
 * from the figure, the dividend's terms and the sets, so it is held to what it was compared
 * against and not to a number written down.
 */
class ASearchHeldToAShareOfItsStepsSaysTheShareTest {

    private static final CompositionBudget STEPS = CompositionBudget.STEPS_A_SEARCH_MAY_TAKE;

    /** How many code points of the string the remainder's dividend weighs. */
    private static final int WEIGHED = 11;

    /** A digit, and a letter that digit alone is followed by: ten sets of code points at each. */
    private static final String A_DIGIT_AND_ITS_LETTER = "(0a|1b|2c|3d|4e|5f|6g|7h|8i|9j)";

    /** The share of the figure each question of the format is held to. */
    private static final int WORK = STEPS.maximum() / (1 + WEIGHED);

    /**
     * A string of eleven digits and then {@code tail}, whose first {@value #WEIGHED} code points,
     * weighed, are divided by {@code divisor}; the remainder and the code points at {@code beside}
     * added up are held against a number.
     */
    private static String model(String tail, int divisor, List<Integer> beside) {
        StringBuilder sum = new StringBuilder();
        for (int index : beside) {
            sum.append("at(codes, ").append(index).append(") + ");
        }
        return """
                module p
                data Code = String
                    invariant String.matches("[0-9]{%d}%s", value)
                behavior pick : (p: Code) -> Int
                let at (codes: List<Int>, i: Int): Int =
                    match List.get(i, codes) with
                        | Some c -> c
                        | None -> 0
                let pick (p) = {
                    let codes = String.codePoints(p.value)
                    let r = Int.floorMod(List.sum(List.mapIndexed((i, x) -> (i + 2) * x,
                        List.take(%d, codes))), %d)
                    if %sr == 300 then 1 else 0
                }
                """.formatted(WEIGHED, tail, WEIGHED, divisor, sum);
    }

    /** The lines of {@code model}'s report naming the steps a search may take. */
    private static List<String> stopsOf(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.OFF));
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors());
        String said = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
        List<String> stops = said.lines().filter(each -> each.contains(STEPS.name() + ","))
                .toList();
        assertFalse(stops.isEmpty(), () -> "the search stops and says so: " + said);
        return stops;
    }

    private static void assertSaidAt(int figure, List<String> stops) {
        for (String each : stops) {
            assertTrue(each.contains("(" + STEPS.name() + ", " + figure + ")"),
                    () -> "at " + figure + ": " + each);
        }
    }

    /**
     * One code point beside the remainder, which the format takes apart into ten sets: each set
     * is walked under a tenth of the question's share, and a divisor of a thousand runs the walk
     * past it.
     */
    @Test
    void aWalkPastWhatEachSetIsWalkedUnderSaysThatPart() {
        int each = WORK / 10;
        assertTrue(each < WORK && WORK < STEPS.maximum(), "three figures apart");
        assertSaidAt(each, stopsOf(model(A_DIGIT_AND_ITS_LETTER, 1000, List.of(WEIGHED))));
    }

    /**
     * Five code points beside the remainder, each taken apart into ten sets: the sets are more
     * than the question's share before anything is walked.
     */
    @Test
    void moreSetsThanTheShareSaysTheShare() {
        assertTrue(Math.pow(10, 5) > WORK, "the sets are past the share");
        assertSaidAt(WORK, stopsOf(model(A_DIGIT_AND_ITS_LETTER.repeat(5), 7,
                List.of(WEIGHED, WEIGHED + 2, WEIGHED + 4, WEIGHED + 6, WEIGHED + 8))));
    }

    /** A divisor past the whole figure is past every share, and the whole figure is said. */
    @Test
    void aDivisorPastTheWholeFigureSaysTheWholeFigure() {
        assertSaidAt(STEPS.maximum(), stopsOf(model("[0-9]", STEPS.maximum() + 1,
                List.of(WEIGHED))));
    }
}
