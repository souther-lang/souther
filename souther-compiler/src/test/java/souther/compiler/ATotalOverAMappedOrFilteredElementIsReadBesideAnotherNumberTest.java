package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A total over a mapped element, or over the elements a filter keeps, is read beside another
 * number as a total over the elements themselves is: the other number is left either way where
 * the total takes a value on each side of it.
 *
 * <p>The total of {@code 2·x} takes the even numbers and the total over a filter takes nought and
 * the numbers from the least it keeps, so neither takes every value of an interval. An order
 * asks a value on each side of a line, which the ends of such a set answer; an equality asks the
 * value itself, and divides the number by the values the total can be.
 */
class ATotalOverAMappedOrFilteredElementIsReadBesideAnotherNumberTest {

    private static final String LINE = "data Line = { qty: Int, code: String }\n";

    private static String model(String parameters, String total, String relation) {
        return """
                module probe
                %s
                behavior check : (%s, cap: Int) -> Bool
                let check (%s, cap) = %s %s cap
                """.formatted(LINE, parameters, parameters.substring(0, parameters.indexOf(':')),
                total, relation);
    }

    private static String report(String model) {
        Compilation compilation = ACompiledModel.measured(model, Adequacy.Asked.fullReport());
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static final String DOUBLED = "List.sum(List.map(x -> x * 2, xs))";
    private static final String FILTERED = "List.sum(List.map(l -> l.qty,"
            + " List.filter(l -> l.qty > 5, lines)))";

    /** Control: the elements as they stand were read before. */
    @Test
    void aPlainTotalIsReadAsItWas() {
        String said = report(model("xs: List<Int>", "List.sum(xs)", "<="));
        assertFalse(said.contains("not read"), said);
    }

    @Test
    void aTotalOfDoubledElementsIsReadBesideAnotherNumberByAnOrder() {
        for (String relation : new String[] {"<=", "<", ">=", ">"}) {
            String said = report(model("xs: List<Int>", DOUBLED, relation));
            assertFalse(said.contains("not read"), relation + "\n" + said);
        }
    }

    @Test
    void aTotalOverWhatAFilterKeepsIsReadBesideAnotherNumberByAnOrder() {
        for (String relation : new String[] {"<=", "<", ">=", ">"}) {
            String said = report(model("lines: List<Line>", FILTERED, relation));
            assertFalse(said.contains("not read"), relation + "\n" + said);
        }
    }

    /**
     * An equality asks the value itself, so it divides the number by what the total takes: it is
     * read as the classes of the numbers the total can be and the numbers it never is, which
     * {@code AnEquationBesideAWeighedNumberIsToldByWhatTheWeighingReachesTest} asks of rows.
     */
    @Test
    void anEqualityBesideAStepsTotalIsReadAsTheClassesItIsTrueAt() {
        for (String said : List.of(report(model("xs: List<Int>", DOUBLED, "==")),
                report(model("lines: List<Line>", FILTERED, "==")))) {
            assertFalse(said.contains("not read"), said);
            assertTrue(said.contains("cap is divided by"), said);
        }
    }

    /** A number added to each element adds as many times as there are elements, so the totals
     *  leave no one remainder and nothing is shown. */
    @Test
    void aNumberAddedToEachElementLeavesNoRemainder() {
        String said = report(model("xs: List<Int>", "List.sum(List.map(x -> x * 2 + 1, xs))", "<="));
        assertTrue(said.contains("not read"), said);
    }
}
