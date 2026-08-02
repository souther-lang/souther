package souther.compiler;

import souther.compiler.diag.Severity;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A relation stated of every element of a container, assumed of the element a combinator's closure is
 * handed (spec §invariant-discharge). {@code List.all(p, xs)} known — as an input type's invariant
 * clause or as a guard the path has asserted — is {@code p} of each element of {@code xs}, so a
 * construction inside a {@code List.map} over {@code xs} reads it and discharges.
 *
 * <p>The counterpart of the rules that carry a property from a container to one built from it: this
 * is the same seam read in the other direction, from the container to the element.
 */
class CompileQuantifiedRelationTest {

    private static long warnings(String module) {
        return Compiler.compileWithWarnings(module).warnings().stream()
                .filter(d -> d.severity() == Severity.WARNING).count();
    }

    @Test
    void aRelationOverEveryElementIsAssumedInsideAMapping() {
        String m = """
                module demo
                data Qty = Int
                    invariant value >= 1
                data Line = { quantity: Int }
                data Cart = { items: List<Line> }
                    invariant List.all(i -> i.quantity >= 1, items)
                behavior toQty : (cart: Cart) -> List<Qty>
                    constructs Qty
                let toQty (cart) = List.map(i -> Qty(i.quantity), cart.items)
                """;
        assertEquals(0, warnings(m),
                "the cart's relation holds of every item, so the element the closure is handed has it");
    }

    @Test
    void aGuardStatingTheSameRelationIsAssumedInsideTheMapping() {
        String m = """
                module demo
                data Qty = Int
                    invariant value >= 1
                data Line = { quantity: Int }
                data Cart = { items: List<Line> }
                behavior toQty : (cart: Cart) -> List<Qty>
                    constructs Qty
                let toQty (cart) =
                    if List.all(i -> i.quantity >= 1, cart.items) then
                        List.map(i -> Qty(i.quantity), cart.items)
                    else
                        []
                """;
        assertEquals(0, warnings(m), "a guard states the relation the same way an invariant does");
    }

    @Test
    void theClosuresOwnNameForTheElementDoesNotMatter() {
        String m = """
                module demo
                data Qty = Int
                    invariant value >= 1
                data Line = { quantity: Int }
                data Cart = { items: List<Line> }
                    invariant List.all(i -> i.quantity >= 1, items)
                behavior toQty : (cart: Cart) -> List<Qty>
                    constructs Qty
                let toQty (cart) = List.map(line -> Qty(line.quantity), cart.items)
                """;
        assertEquals(0, warnings(m), "the relation is read at the element, whatever it is called");
    }

    @Test
    void theUnqualifiedSpellingStatesTheSameRelation() {
        String m = """
                module demo
                import List ( all, map )
                data Qty = Int
                    invariant value >= 1
                data Line = { quantity: Int }
                data Cart = { items: List<Line> }
                    invariant all(i -> i.quantity >= 1, items)
                behavior toQty : (cart: Cart) -> List<Qty>
                    constructs Qty
                let toQty (cart) = map(i -> Qty(i.quantity), cart.items)
                """;
        assertEquals(0, warnings(m), "an import drops the qualifier and nothing else");
    }

    @Test
    void aRelationOverBareValuesIsAssumedAtTheElement() {
        String m = """
                module demo
                data Qty = Int
                    invariant value >= 1
                data Cart = { quantities: List<Int> }
                    invariant List.all(q -> q >= 1, quantities)
                behavior toQty : (cart: Cart) -> List<Qty>
                    constructs Qty
                let toQty (cart) = List.map(q -> Qty(q), cart.quantities)
                """;
        assertEquals(0, warnings(m), "an element with no type of its own carries the relation too");
    }

    @Test
    void aHelperExpandedIntoTheClosureReadsTheRelation() {
        String m = """
                module demo
                data Qty = Int
                    invariant value >= 1
                data Line = { quantity: Int }
                data Cart = { items: List<Line> }
                    invariant List.all(i -> i.quantity >= 1, items)
                let toOne (q: Int): Qty = Qty(q)
                behavior toQty : (cart: Cart) -> List<Qty>
                    constructs Qty
                let toQty (cart) = List.map(i -> toOne(i.quantity), cart.items)
                """;
        assertEquals(0, warnings(m),
                "a helper stands where it was called, which is inside the closure");
    }

    @Test
    void anElementOfASelectionCarriesTheRelation() {
        String m = """
                module demo
                data Qty = Int
                    invariant value >= 1
                data Line = { quantity: Int, taxable: Bool }
                data Cart = { items: List<Line> }
                    invariant List.all(i -> i.quantity >= 1, items)
                behavior toQty : (cart: Cart) -> List<Qty>
                    constructs Qty
                let toQty (cart) =
                    List.map(i -> Qty(i.quantity), List.filter(i -> i.taxable, cart.items))
                """;
        assertEquals(0, warnings(m), "a selection holds only elements the relation was stated of");
    }

    @Test
    void anElementOfAFoldCarriesTheRelation() {
        String m = """
                module demo
                data Qty = Int
                    invariant value >= 1
                data Line = { quantity: Int }
                data Cart = { items: List<Line> }
                    invariant List.all(i -> i.quantity >= 1, items)
                behavior first : (cart: Cart) -> List<Qty>
                    constructs Qty
                let first (cart) = List.fold((acc, i) -> acc ++ [Qty(i.quantity)], [], cart.items)
                """;
        assertEquals(0, warnings(m), "a fold is handed the elements a mapping is handed");
    }

    @Test
    void aRelationOverNestedContainersReachesTheInnerElement() {
        String m = """
                module demo
                data Qty = Int
                    invariant value >= 1
                data Line = { quantity: Int }
                data Group = { lines: List<Line> }
                data Cart = { groups: List<Group> }
                    invariant List.all(g -> List.all(i -> i.quantity >= 1, g.lines), groups)
                behavior toQty : (cart: Cart) -> List<List<Qty>>
                    constructs Qty
                let toQty (cart) =
                    List.map(g -> List.map(i -> Qty(i.quantity), g.lines), cart.groups)
                """;
        assertEquals(0, warnings(m),
                "the relation the outer element carries is itself stated of every inner element");
    }

    @Test
    void aRelationOverAnotherContainerIsNotAssumed() {
        String m = """
                module demo
                data Qty = Int
                    invariant value >= 1
                data Line = { quantity: Int }
                data Cart = { items: List<Line>, spares: List<Line> }
                    invariant List.all(i -> i.quantity >= 1, items)
                behavior toQty : (cart: Cart) -> List<Qty>
                    constructs Qty
                let toQty (cart) = List.map(i -> Qty(i.quantity), cart.spares)
                """;
        assertEquals(1, warnings(m), "nothing was stated of the spares");
    }

    @Test
    void aRelationOfSomeElementIsNotAssumedOfEach() {
        String m = """
                module demo
                data Qty = Int
                    invariant value >= 1
                data Line = { quantity: Int }
                data Cart = { items: List<Line> }
                    invariant List.any(i -> i.quantity >= 1, items)
                behavior toQty : (cart: Cart) -> List<Qty>
                    constructs Qty
                let toQty (cart) = List.map(i -> Qty(i.quantity), cart.items)
                """;
        assertEquals(1, warnings(m), "one element having it says nothing about the rest");
    }

    @Test
    void aRelationDeniedIsNotAssumed() {
        String m = """
                module demo
                data Qty = Int
                    invariant value >= 1
                data Line = { quantity: Int }
                data Cart = { items: List<Line> }
                behavior toQty : (cart: Cart) -> List<Qty>
                    constructs Qty
                let toQty (cart) =
                    if List.all(i -> i.quantity >= 1, cart.items) then
                        []
                    else
                        List.map(i -> Qty(i.quantity), cart.items)
                """;
        assertEquals(1, warnings(m), "some element failing it leaves every element unsettled");
    }

    @Test
    void aMappedElementDoesNotCarryTheRelationOfWhatWasMapped() {
        String m = """
                module demo
                data Qty = Int
                    invariant value >= 1
                data Line = { quantity: Int }
                data Cart = { items: List<Line> }
                    invariant List.all(i -> i.quantity >= 1, items)
                behavior toQty : (cart: Cart) -> List<Qty>
                    constructs Qty, Line
                let toQty (cart) =
                    List.map(i -> Qty(i.quantity), List.map(i -> Line { quantity = 0 }, cart.items))
                """;
        assertEquals(1, warnings(m), "what a mapping makes is not what the relation was stated of");
    }

    @Test
    void aRelationIsDroppedWhereItsContainerIsRebound() {
        String m = """
                module demo
                data Qty = Int
                    invariant value >= 1
                data Line = { quantity: Int }
                data Group = { items: List<Line> }
                data Cart = { items: List<Line>, groups: List<Group> }
                    invariant List.all(i -> i.quantity >= 1, items)
                behavior toQty : (cart: Cart) -> List<List<Qty>>
                    constructs Qty
                let toQty (cart) =
                    List.map(cart -> List.map(i -> Qty(i.quantity), cart.items), cart.groups)
                """;
        assertEquals(1, warnings(m),
                "inside the closure `cart.items` is the group's, and nothing was stated of that");
    }
}
