package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A row's value at a position it is not about is exchanged for one that lets the body go on, where
 * the value it was first composed with is what stopped the body at a guard.
 *
 * <p>The row for a class of {@code kind} is about {@code kind}. Composed from the classes alone,
 * {@code amount} stands at the first class it has, which fails {@code amount > 0}, and every such
 * row answers {@code Refused} before {@code kind} is read: the class counts as covered by a row that
 * says nothing about it. Run, the row is seen leaving the guard, and the way into the rest of the
 * block says what {@code amount} has to be for the body to go on.
 *
 * <p>And the row for the class that fails the guard keeps it. That row is about the value the
 * guard refuses, and stopping there is what it is for.
 */
class AFillerThatStopsTheBodyIsExchangedForOneThatGoesOnTest {

    private static final String MODEL = """
            module example.settle

            data Plain
            data Express
            data Kind = Plain | Express

            data Done = { n: Int }
            data Refused

            behavior settle : (kind: Kind, amount: Int) -> Done | Refused
                constructs Done

            let settle (kind, amount) = {
                guard amount > 0 else Refused
                match kind with
                    | Plain -> Done { n = amount }
                    | Express -> Done { n = amount + 500 }
            }
            """;

    /** The rows about {@code kind} are past the guard. */
    @Test
    void aRowAboutAnotherPositionGoesOnPastTheGuard() {
        Map<String, String> rows = rowsOf(MODEL);
        assertEquals("Plain, 1", rows.get("kind=Plain"));
        assertEquals("Express, 1", rows.get("kind=Express"));
    }

    /** The row about the class the guard refuses still stops there. */
    @Test
    void aRowAboutTheClassTheGuardRefusesKeepsIt() {
        assertEquals("Plain, 0", rowsOf(MODEL).get("amount=x <= 0"));
    }

    /**
     * A guard on what the elements of a list add up to, read through a helper.
     *
     * <p>No position holds the total, and the amount of an element is not a position anything
     * divides either: the value a row is composed with puts the least amount there is in every
     * element. So what gets a row past the guard is a demand on the list as a whole, and the list
     * is composed to meet it — with what the row's classes ask of each element held in it.
     */
    private static final String A_TOTAL = """
            module example.settle

            data Plain
            data Express
            data Kind = Plain | Express

            data Amount = Int
                invariant value >= 0

            data Self
            data Company
            data Payer = Self | Company

            data Item = { amount: Amount, payer: Payer }

            data Done = { n: Int }
            data Refused

            behavior settle : (kind: Kind, items: List<Item>) -> Done | Refused
                constructs Done

            let total (items: List<Item>): Int = List.sum(List.map(i -> i.amount.value, items))

            let settle (kind, items) = {
                guard total(items) > 0 else Refused
                match kind with
                    | Plain -> Done { n = total(items) }
                    | Express -> Done { n = total(items) + 500 }
            }
            """;

    /** The rows about {@code kind} hold a list whose amounts come to more than nothing. */
    @Test
    void aRowAboutAnotherPositionGoesOnPastAGuardOnATotal() {
        Map<String, String> rows = rowsOf(A_TOTAL);
        assertEquals("Plain, [Item { amount = Amount(1), payer = Self }]", rows.get("kind=Plain"));
    }

    /**
     * And a row about a class of the elements keeps that class in every element while the list is
     * composed to the total.
     */
    @Test
    void aRowAboutAClassOfTheElementsKeepsItWhileTheListComesToTheTotal() {
        assertEquals("Plain, [Item { amount = Amount(1), payer = Company }]",
                rowsOf(A_TOTAL).get("items[*].payer=Company"));
    }

    /** What each row is for, by its label, and what it writes. */
    private static Map<String, String> rowsOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, Adequacy.Filling> all = Adequacy.generatedOf(compilation.db(), "example.settle");
        assertNotNull(all, "the model under test compiles");
        Map<String, String> out = new LinkedHashMap<>();
        for (Generator.GeneratedRow row : all.get("settle").composed().rows()) {
            String written = String.join(", ", row.inputs().stream().map(i -> i.text()).toList());
            for (Generator.Purpose purpose : row.purposes()) {
                if (purpose instanceof Generator.Purpose.ForAClass forAClass) {
                    out.put(forAClass.label(), written);
                }
            }
        }
        return out;
    }
}
