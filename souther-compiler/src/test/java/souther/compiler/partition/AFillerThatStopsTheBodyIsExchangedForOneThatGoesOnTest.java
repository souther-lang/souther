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

    /**
     * A fork above the guard, which the row goes through the false way and goes on from.
     *
     * <p>Its comparison comes out the false way in the run as the guard's does, and it is not what
     * stopped the row: the row went on past it. Held to it, the row would be sent the other way
     * round a fork that let it go on, and the guard that refused it would be what nothing was held
     * to.
     */
    private static final String A_FORK_ABOVE = """
            module example.settle

            data Plain
            data Express
            data Kind = Plain | Express

            data Done = { n: Int }
            data Refused

            behavior settle : (kind: Kind, earlier: Int, amount: Int) -> Done | Refused
                constructs Done

            let settle (kind, earlier, amount) = {
                let bonus = if earlier > 0 then 100 else 0
                guard amount > 0 else Refused
                match kind with
                    | Plain -> Done { n = amount + bonus }
                    | Express -> Done { n = amount + bonus + 500 }
            }
            """;

    /** The row about {@code kind} is held to the guard's comparison, and goes the same way round
     *  the fork above it as it did. */
    @Test
    void aRowIsHeldToTheGuardThatStoppedItAndNotToAForkAboveIt() {
        assertEquals("Plain, 0, 1", rowsOf(A_FORK_ABOVE).get("kind=Plain"));
    }

    /**
     * A guard that lets the body go on where its comparison comes out false.
     *
     * <p>{@code amount = 0} makes {@code amount <= 0} hold and the guard refuse. What gets a row
     * past is the comparison failing, which a repair that took every guard's comparison to be one
     * that has to hold could not ask for.
     */
    @Test
    void aRowIsHeldToTheWayTheGuardsComparisonHasToComeOut() {
        Map<String, String> rows =
                rowsOf(MODEL.replace("guard amount > 0", "guard Bool.not(amount <= 0)"));
        assertEquals("Plain, 1", rows.get("kind=Plain"));
        assertEquals("Plain, 0", rows.get("amount=x <= 0"), "the row about the refused class");
    }

    private static final String TWO_AMOUNTS = """
            module example.settle

            data Plain
            data Express
            data Kind = Plain | Express

            data Done = { n: Int }
            data Refused

            behavior settle : (kind: Kind, a: Int, b: Int) -> Done | Refused
                constructs Done

            let settle (kind, a, b) = {
                guard CONDITION else Refused
                match kind with
                    | Plain -> Done { n = a + b }
                    | Express -> Done { n = a + b + 500 }
            }
            """;

    /**
     * Both sides of an {@code &&} at once. A row that stops at the first is not past the guard
     * once the first holds — the second refuses it then — so what is asked for is the way whole.
     *
     * <p>The second side on a total, which no class of a position gives a row the way to: held to
     * the first side alone, the search finds nothing past the guard however it walks the classes.
     */
    @Test
    void aWayPastAGuardIsEveryComparisonItTakesAtOnce() {
        String both = A_TOTAL
                .replace("(kind: Kind, items: List<Item>)", "(kind: Kind, a: Int, items: List<Item>)")
                .replace("let settle (kind, items)", "let settle (kind, a, items)")
                .replace("guard total(items) > 0", "guard a > 0 && total(items) > 0");
        assertEquals("Plain, 1, [Item { amount = Amount(1), payer = Self }]",
                rowsOf(both).get("kind=Plain"));
    }

    /** Either side of an {@code ||}, and one is enough: the row is moved at one position. */
    @Test
    void aGuardWithTwoWaysPastIsPassedByOne() {
        assertEquals("Plain, 1, 0",
                rowsOf(TWO_AMOUNTS.replace("CONDITION", "a > 0 || b > 0")).get("kind=Plain"));
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
