package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.TestDay;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.TermPath;
import souther.compiler.observe.Figure;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.types.Type;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A value composed with the collections of a parameter holding the numbers they are asked to is a
 * try, whether it comes to a value or not: where none does, the tries are what the figure counts,
 * and the search says it stopped at the figure when ways are left.
 *
 * <p>Asked of a type no value holds a number in, so that every try is one that comes to nothing and
 * the count of tries is all there is to see.
 */
class EveryValueComposedForAnAimIsATryAgainstTheFigureTest {

    private static final String MODULE = """
            module example.aims

            data Ok
            """;

    private static List<RowAims.Aim> aims(int count) {
        List<RowAims.Aim> out = new ArrayList<>();
        for (int at = 0; at < count; at++) {
            out.add(new RowAims.Aim(TermPath.of("p").then("f" + at),
                    List.of(BigInteger.valueOf(-1), BigInteger.ONE, BigInteger.TWO,
                            BigInteger.TEN)));
        }
        return out;
    }

    private static Set<Figure> stoppedAt(int aims) {
        Compilation compilation = Compilation.ofSource(MODULE, "Main");
        RuleReadingContext reading = RuleReadingContext.unshared(
                RuleReadings.of(compilation, compilation.modules().get(0)),
                ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
        Set<Figure> stopped = new LinkedHashSet<>();
        List<FixtureTemplate> built = RowSearch.aimedAt("p", Type.INT, aims(aims), reading,
                stopped);
        assertEquals(List.of(), built);
        return stopped;
    }

    /** Nine collections of four numbers are four to the ninth ways: the tries stop at the figure. */
    @Test
    void waysLeftWhenTheTriesRunOutAreSaidToBeLeft() {
        assertTrue(stoppedAt(9).contains(
                CompositionBudget.VALUES_AN_ELEMENT_IS_CHOSEN_AMONG.figure()));
    }

    /** Two collections are sixteen ways and four each alone, all of them tried. */
    @Test
    void waysAllTriedAreSaidToBeNoneLeft() {
        assertFalse(stoppedAt(2).contains(
                CompositionBudget.VALUES_AN_ELEMENT_IS_CHOSEN_AMONG.figure()));
    }
}
