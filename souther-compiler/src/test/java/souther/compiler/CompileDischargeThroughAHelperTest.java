package souther.compiler;

import souther.compiler.diag.Severity;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What an input's type guarantees, read where a helper put the construction (spec
 * §invariant-discharge). A helper's argument becomes a binding and the parameter's reads become
 * reads of that binding, so a construction moved into a helper reads a name the seeding never wrote.
 * A binding given a location <em>is</em> that location, which is how the two meet.
 */
class CompileDischargeThroughAHelperTest {

    private static long warnings(String module) {
        return Compiler.compileWithWarnings(module).warnings().stream()
                .filter(d -> d.severity() == Severity.WARNING).count();
    }

    @Test
    void aTypesOwnRelationSurvivesAHelperTakingTheRecord() {
        String m = """
                module demo
                data Qty = Int
                    invariant value >= 1
                data Cart = { quantity: Int }
                    invariant quantity >= 1
                let one (c: Cart): Qty = Qty(c.quantity)
                behavior toQty : (cart: Cart) -> Qty
                    constructs Qty
                let toQty (cart) = one(cart)
                """;
        assertEquals(0, warnings(m), "`c` is `cart`, so `c.quantity` is the term the seeding wrote");
    }

    @Test
    void aGuardSurvivesAHelperTakingTheRecord() {
        String m = """
                module demo
                data Qty = Int
                    invariant value >= 1
                data TooSmall
                data Cart = { quantity: Int }
                let one (c: Cart): Qty = Qty(c.quantity)
                behavior toQty : (cart: Cart) -> Qty | TooSmall
                    constructs Qty, TooSmall
                let toQty (cart) = {
                    guard cart.quantity >= 1
                        else TooSmall
                    one(cart)
                }
                """;
        assertEquals(0, warnings(m), "a guard settles the same term the helper's body reads");
    }

    @Test
    void anElementTypesRelationSurvivesAHelperTakingTheRecord() {
        String m = """
                module demo
                data Pos = Int
                    invariant value >= 1
                data Qty = Int
                    invariant value >= 1
                data Line = { quantity: Pos }
                data Cart = { items: List<Line> }
                let toOne (line: Line): Qty = Qty(line.quantity.value)
                behavior toQty : (cart: Cart) -> List<Qty>
                    constructs Qty
                let toQty (cart) = List.map(i -> toOne(i), cart.items)
                """;
        assertEquals(0, warnings(m), "the element seeded inside the closure is what the helper reads");
    }

    @Test
    void aRelationOverEveryElementSurvivesAHelperTakingTheRecord() {
        String m = """
                module demo
                data Qty = Int
                    invariant value >= 1
                data Line = { quantity: Int }
                data Cart = { items: List<Line> }
                    invariant List.all(i -> i.quantity >= 1, items)
                let toOne (line: Line): Qty = Qty(line.quantity)
                behavior toQty : (cart: Cart) -> List<Qty>
                    constructs Qty
                let toQty (cart) = List.map(i -> toOne(i), cart.items)
                """;
        assertEquals(0, warnings(m), "the relation reaches the element the helper is handed");
    }

    @Test
    void aChainOfBindingsReadsTheLocationAtTheEndOfIt() {
        String m = """
                module demo
                data Qty = Int
                    invariant value >= 1
                data Cart = { quantity: Int }
                    invariant quantity >= 1
                behavior toQty : (cart: Cart) -> Qty
                    constructs Qty
                let toQty (cart) = {
                    let a = cart
                    let b = a
                    Qty(b.quantity)
                }
                """;
        assertEquals(0, warnings(m), "each binding is what it was given, down the chain");
    }

    @Test
    void aBindingGivenSomethingThatIsNotALocationNamesItself() {
        String m = """
                module demo
                data Qty = Int
                    invariant value >= 1
                data Cart = { quantity: Int }
                    invariant quantity >= 1
                data Other = { quantity: Int }
                behavior toQty : (cart: Cart, other: Other, pick: Bool) -> Qty
                    constructs Qty
                let toQty (cart, other, pick) = {
                    let c = if pick then cart.quantity else other.quantity
                    Qty(c)
                }
                """;
        assertEquals(1, warnings(m), "a choice of two is neither of them");
    }

    @Test
    void aBindingWhoseLocationIsTakenOverNamesItselfAgain() {
        String m = """
                module demo
                data Pos = Int
                    invariant value >= 1
                data Qty = Int
                    invariant value >= 1
                data Line = { quantity: Pos }
                data Cart = { quantity: Int, items: List<Line> }
                behavior toQty : (cart: Cart) -> List<Qty>
                    constructs Qty
                let toQty (cart) = {
                    let c = cart
                    List.map(cart -> Qty(c.quantity), cart.items)
                }
                """;
        assertEquals(1, warnings(m),
                "`c` is the outer cart, and inside the closure the name it was given is the element");
    }
}
