package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A combination of two classes that the declarations leave no value for is not one a row is owed.
 *
 * <p>{@code a < b} holds {@code b} above {@code a}. The classes come from two comparisons that
 * each relate one of the two to a number of its own, which no rule between {@code a} and
 * {@code b} is about, so each is divided apart.
 */
class TwoClassesARuleLeavesNoRoomForAreNotOwedTogetherTest {

    /**
     * {@code a} from 1000 has no {@code b} under 500. The combinations that can be written, and
     * the ones with a number no rule relates to either, stay owed.
     */
    @Test
    void aCombinationTheDeclaredRuleBetweenTwoPositionsRulesOutIsNotOwedARow() {
        String report = about("four.a.value + four.c.value >= 1000",
                "four.b.value + four.d.value < 500", "B");

        String a = "`four.a: 1000 <= x <= 1439` at f/four.a with ";
        assertFalse(report.contains(a + "`four.b: 1 <= x < 500` at f/four.b"), report);
        assertTrue(report.contains(a + "`four.b: 500 <= x <= 1440` at f/four.b"), report);
        assertTrue(report.contains(a + "`four.c: 0 <= x < 1000` at f/four.c"), report);
    }

    /**
     * The one pair that can be written is the one the ends of both classes make: {@code a} at
     * 1000, the least of its class, and {@code b} at 1001, the greatest below the end of its. A
     * class taken in short of either end would lose it.
     */
    @Test
    void aCombinationThatCanBeWrittenAtTheEndsOfBothClassesIsStillOwed() {
        String report = about("four.a.value + four.c.value >= 1000",
                "four.b.value + four.d.value > 1001", "C");

        assertTrue(report.contains("`four.a: 1000 <= x <= 1439` at f/four.a with "
                + "`four.b: 1 <= x < 1002` at f/four.b"), report);
    }

    /** The report of a behavior that takes {@code A} where {@code first} holds, else {@code B}
     *  where {@code second} does, else {@code C}; its example is the row at 10, 20, 30 and 40,
     *  which comes out as {@code outcome}. */
    private static String about(String first, String second, String outcome) {
        Compilation compilation = ACompiledModel.measured("""
                module example.four

                data Minute = Int
                    invariant withinDay = value >= 0 && value <= 1440

                data Four =
                    { a: Minute
                    , b: Minute
                    , c: Minute
                    , d: Minute
                    }
                    invariant bAfterA = a < b

                data A
                data B
                data C

                behavior f : (four: Four) -> A | B | C

                let f (four) =
                    if %s
                        then A
                        else if %s then B else C

                example f
                    | "x" : (Four { a = Minute(10), b = Minute(20), c = Minute(30), d = Minute(40) })
                        -> %s
                """.formatted(first, second, outcome), Adequacy.Asked.fullReport());
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
