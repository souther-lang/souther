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
 * <p>{@code a < b} holds {@code b} above {@code a}, so {@code a} from 1000 up has no {@code b}
 * under 500. The classes come from two comparisons that each relate one of the two to a number
 * of its own, which no rule between {@code a} and {@code b} is about, so each is divided apart.
 */
class TwoClassesARuleLeavesNoRoomForAreNotOwedTogetherTest {

    private static final String A_FROM_1000 = "`four.a: 1000 <= x <= 1439` at f/four.a with ";
    private static final String B_BELOW_500 = "`four.b: 1 <= x < 500` at f/four.b";
    private static final String B_FROM_500 = "`four.b: 500 <= x <= 1440` at f/four.b";

    @Test
    void aCombinationTheDeclaredRuleBetweenTwoPositionsRulesOutIsNotOwedARow() {
        String report = about();

        assertFalse(report.contains(A_FROM_1000 + B_BELOW_500), report);
        assertTrue(report.contains(A_FROM_1000 + B_FROM_500), report);
        assertTrue(report.contains("`four.a: 0 <= x < 1000` at f/four.a with " + B_FROM_500),
                report);
    }

    private static String about() {
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
                    if four.a.value + four.c.value >= 1000
                        then A
                        else if four.b.value + four.d.value < 500 then B else C

                example f
                    | "x" : (Four { a = Minute(10), b = Minute(20), c = Minute(30), d = Minute(40) })
                        -> B
                """, Adequacy.Asked.fullReport());
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
