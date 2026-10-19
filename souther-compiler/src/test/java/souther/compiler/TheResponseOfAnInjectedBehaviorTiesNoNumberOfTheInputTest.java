package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What an injected behavior answers is a value nothing relates to the input, so a guard on it ties
 * no two numbers of a later comparison, and a number made of its elements is one a comparison is
 * read against as it is for an input.
 */
class TheResponseOfAnInjectedBehaviorTiesNoNumberOfTheInputTest {

    private static final String GUARDED = """
            module example.guarded

            data Username = String
                invariant String.length(value) >= 1 && String.length(value) <= 40
            data User = { username: Username }
            data Stop
            data Taken

            behavior isFree : (n: Username) -> Bool

            behavior update : (current: User, wanted: User, other: Username) -> User | Stop | Taken
                depends on isFree
            let update (current, wanted, other, isFree) = {
                guard isFree(other) else Stop
                guard wanted.username == current.username else Taken
                wanted
            }
            """;

    private static final String SUMMED = """
            module example.summed

            data Item = { sku: String, quantity: Int }
            data Cart = { items: List<Item> }
            data Snap = { rows: List<Item> }
            behavior readSnap : (order: Cart) -> Snap
                constructs Snap
            behavior covered : (order: Cart) -> Bool
                depends on readSnap

            let covered (order, readSnap) = {
              let n = List.sum(List.map(.quantity, readSnap(order).rows))
              List.all(i -> n >= i.quantity, order.items)
            }
            """;

    private static final String LOOKED_UP = """
            module example.looked

            import List ( all, indexBy )

            data Sku = String
            data Eaches = Int
                invariant value >= 0
            data LineItem = { sku: Sku, quantity: Int }
            data Cart = { items: List<LineItem> }
            data StockLine = { sku: Sku, quantity: Eaches }
            data StockSnapshot = { rows: List<StockLine> }
                invariant List.allDistinctBy(.sku, rows)
            data Allocated = { total: Int }
            data InsufficientStock

            behavior readStock : (order: Cart) -> StockSnapshot
                constructs StockSnapshot, StockLine
            behavior commitStock : (order: Cart) -> Allocated
                constructs Allocated

            let onHand (snap: StockSnapshot): Map<Sku, StockLine> = indexBy(.sku, snap.rows)

            let currentStock (stock: Map<Sku, StockLine>, sku: Sku): Eaches =
                Map.get(sku, stock) |> Option.map(.quantity) |> Option.withDefault(Eaches(0))

            let allocatable (i: LineItem, stock: Map<Sku, StockLine>): Bool =
                currentStock(stock, i.sku) >= Eaches(i.quantity)

            behavior allocate : (order: Cart) -> Allocated | InsufficientStock
                depends on readStock, commitStock

            let allocate (order, readStock, commitStock) = {
                let stock = onHand(readStock(order))
                guard all(i -> allocatable(i, stock), order.items)
                    else InsufficientStock
                commitStock(order)
            }
            """;

    private static final String TWO_KEYS = LOOKED_UP.replace("module example.looked",
            "module example.twokeys") + """

            behavior lessThan : (order: Cart, a: Sku, b: Sku) -> Bool
                depends on readStock

            let lessThan (order, a, b, readStock) = {
                let stock = onHand(readStock(order))
                currentStock(stock, a) < currentStock(stock, b)
            }
            """;

    private static final String CHOSEN = """
            module example.chosen

            data Username = String
                invariant String.length(value) >= 1 && String.length(value) <= 40
            data User = { username: Username }
            data NotFound
            data Taken

            behavior findUserByName : (name: Username) -> User | NotFound
                constructs User

            behavior rename : (current: User, wanted: User) -> User | Taken
                depends on findUserByName
            let rename (current, wanted, findUserByName) = {
                let free =
                    if wanted.username == current.username
                    then true
                    else match findUserByName(wanted.username) with
                             | User     -> false
                             | NotFound -> true
                guard free else Taken
                wanted
            }
            """;

    private static String reportOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    @Test
    void aGuardOnTheResponseLeavesALaterComparisonRead() {
        String report = reportOf(GUARDED);

        assertFalse(report.contains("not read: comparison"), report);
        assertFalse(report.contains("not accounted for: comparison"), report);
    }

    @Test
    void anEntryLookedUpInAMapFiledFromTheResponsesListIsANumberAComparisonIsReadAgainst() {
        String report = reportOf(LOOKED_UP);

        assertFalse(report.contains("not read: comparison"), report);
        assertFalse(report.contains("not read: fork"), report);
        assertFalse(report.contains("not accounted for"), report);
        // The entry under a key is the last element of that key, and the cases of a key held twice
        // are the ones no row measures.
        assertTrue(report.contains("allocate — read what this measure went without"), report);
    }

    @Test
    void theEntryUnderAKeyIsTheLastOfItsKeyWhereTheResponseMayHoldAKeyTwice() {
        String report = reportOf(LOOKED_UP.replace("module example.looked", "module example.twice")
                .replace("\n    invariant List.allDistinctBy(.sku, rows)", ""));

        assertFalse(report.contains("not read"), report);
        assertTrue(report.contains("allocate — read what this measure went without"), report);
    }

    @Test
    void twoAnswersOfOneWrittenCallAreNotTakenForOneContainer() {
        String report = reportOf(LOOKED_UP.replace("module example.looked", "module example.apart")
                .replace("    commitStock(order)\n}", "    commitStock(order)\n}\n"
                        + "\nlet stockOf (order: Cart) = onHand(readStock(order))\n"
                        + "\nbehavior lessThan : (one: Cart, other: Cart, k: Sku) -> Bool\n"
                        + "    depends on readStock\n"
                        + "\nlet lessThan (one, other, k, readStock) =\n"
                        + "    currentStock(stockOf(one), k) < currentStock(stockOf(other), k)\n"));

        assertFalse(report.contains("not read: comparison@"), report);
    }

    @Test
    void twoEntriesLookedUpInOneMapAreNeverTakenForOneValue() {
        String report = reportOf(TWO_KEYS);

        assertTrue(report.contains("not read: comparison"), report);
    }

    @Test
    void aMatchOnTheResponseBeforeAComparisonLeavesItRead() {
        String report = reportOf(CHOSEN);

        assertFalse(report.contains("not read"), report);
        assertFalse(report.contains("not accounted for"), report);
    }

    @Test
    void aSumOfWhatIsMadeOfEachElementOfTheResponseIsAlsoReadAgainst() {
        String report = reportOf(SUMMED.replace("module example.summed", "module example.made")
                .replace(".quantity, readSnap", "i -> i.quantity + 1, readSnap"));

        assertFalse(report.contains("not read: comparison"), report);
        assertFalse(report.contains("not accounted for: comparison"), report);
    }

    @Test
    void aSumOfAnInputNumberAddedForEachElementOfTheResponseIsNotTakenForASumOfTheResponse() {
        String report = reportOf(SUMMED.replace("module example.summed", "module example.beside")
                .replace("data Cart = { items: List<Item> }",
                        "data Cart = { items: List<Item>, extra: Int }")
                .replace(".quantity, readSnap", "i -> i.quantity + order.extra, readSnap"));

        assertTrue(report.contains("not read: comparison"), report);
    }

    @Test
    void aSumOfTheResponsesElementsIsANumberAComparisonIsReadAgainst() {
        String report = reportOf(SUMMED);

        assertFalse(report.contains("not read: comparison"), report);
        assertFalse(report.contains("not accounted for: comparison"), report);
    }
}
