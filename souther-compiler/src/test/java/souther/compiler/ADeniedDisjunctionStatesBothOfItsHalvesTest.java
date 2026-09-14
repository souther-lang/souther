package souther.compiler;

import souther.compiler.diag.Severity;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a rule written as a denied disjunction states, which is both of its halves denied.
 *
 * <p>One connective and one polarity say what a condition gives its reader, and the answer does not
 * depend on which of the two ways round they arrive: a conjunction stated and a disjunction denied
 * each give both halves. A reading that takes a conjunction apart and stops at a disjunction states
 * nothing about a rule an author wrote the other way round, and the rule is then owed a run-time
 * check where the values already settle it.
 *
 * <p>What is asked here is the polarity as much as the connective. A disjunction denied gives both
 * halves <em>denied</em>, so a quantifier under one is a quantifier said to fail of some element,
 * which names no element and is not recorded — and a denial inside one of the halves states the
 * quantifier again.
 */
class ADeniedDisjunctionStatesBothOfItsHalvesTest {

    private static long warnings(String module) {
        return Compiler.compileWithWarnings(module).warnings().stream()
                .filter(d -> d.severity() == Severity.WARNING).count();
    }

    /** A rule of a type, written as a denied disjunction of two orders. Each half denied is an
     *  order the guards settle, so nothing is left for a run-time check. */
    @Test
    void aDeniedDisjunctionOwesBothOfItsHalvesDenied() {
        String m = """
                module demo
                data TooSmall
                data Qty = Int
                    invariant Bool.not(value < 1 || value > 10)
                behavior toQty : (n: Int) -> Qty | TooSmall
                    constructs Qty
                let toQty (n) = {
                    guard n >= 1
                        else TooSmall
                    guard n <= 10
                        else TooSmall
                    Qty(n)
                }
                """;
        assertEquals(0, warnings(m),
                "both halves denied are the two orders the guards settle");
    }

    /** The same rule written as the conjunction it means, which is the reading the one above has to
     *  agree with. Two ways of writing one rule are one rule. */
    @Test
    void theConjunctionItMeansIsOwedTheSame() {
        String m = """
                module demo
                data TooSmall
                data Qty = Int
                    invariant value >= 1 && value <= 10
                behavior toQty : (n: Int) -> Qty | TooSmall
                    constructs Qty
                let toQty (n) = {
                    guard n >= 1
                        else TooSmall
                    guard n <= 10
                        else TooSmall
                    Qty(n)
                }
                """;
        assertEquals(0, warnings(m), "the two orders the guards settle");
    }

    /** A denied disjunction of two quantifiers records neither of them: what it states is that each
     *  fails of some element, and which element is not something this check can name. */
    @Test
    void aDeniedDisjunctionOfQuantifiersRecordsNeitherOfThem() {
        String m = """
                module demo
                data Pos = Int
                    invariant value >= 1
                data Line = { qty: Int, price: Int }
                data Cart = { items: List<Line> }
                    invariant Bool.not(List.all(x -> x.qty >= 1, items)
                        || List.all(x -> x.price >= 1, items))
                behavior toPos : (cart: Cart) -> List<Pos>
                    constructs Pos
                let toPos (cart) = List.map(i -> Pos(i.qty), cart.items)
                """;
        assertEquals(1, warnings(m),
                "a quantifier said to fail of some element states nothing of the element built from");
    }

    /** And a denied disjunction of two denied quantifiers records both: the denial inside each half
     *  meets the denial the disjunction carries into it, and what is left is the quantifier. */
    @Test
    void aDeniedDisjunctionOfDeniedQuantifiersRecordsBothOfThem() {
        String m = """
                module demo
                data Pos = Int
                    invariant value >= 1
                data Line = { qty: Int, price: Int }
                data Cart = { items: List<Line> }
                    invariant Bool.not(Bool.not(List.all(x -> x.qty >= 1, items))
                        || Bool.not(List.all(x -> x.price >= 1, items)))
                behavior toPos : (cart: Cart) -> List<Pos>
                    constructs Pos
                let toPos (cart) = List.map(i -> Pos(i.qty), cart.items)
                """;
        assertEquals(0, warnings(m), "every element's qty is at least one, which the rule states");
        assertEquals(0, warnings(m.replace("Pos(i.qty)", "Pos(i.price)")),
                "and so is every element's price, which is the other half of the same rule");
    }
}
