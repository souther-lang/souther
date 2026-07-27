package souther.compiler.frontend;

import souther.compiler.ast.Ast;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A module's declarations can be taken back out of the source it was parsed from, each under the
 * name it declares. This is how a module publishes what it declares: the text goes into the jar and
 * the importing project parses it back, rather than reading a second description of the same syntax.
 */
class CstSlicesTest {

    @Test
    void everyDeclarationOfAModuleIsAccountedFor() {
        CstFrontend.Parsed parsed = CstFrontend.parseWithSlices("""
                module shop.cart exposing ( Sku, LineItem, Cart, Empty, quote )
                import String ( length )

                data Sku = String
                    invariant length(value) >= 1

                data LineItem =
                    { sku: Sku
                    , quantity: Int
                    }
                    invariant quantity >= 0

                data Cart = { items: List<LineItem> }
                data Empty

                behavior quote : (c: Cart) -> Cart | Empty constructs Cart, Empty
                let quote (c) = if List.length(c.items) >= 1 then c else Empty

                let itemCount (c: Cart) = List.length(c.items)
                """, null);

        Ast.Module module = parsed.module();
        CstFrontend.Slices slices = parsed.slices();
        assertEquals(module.imports().size(), slices.imports().size());
        assertEquals(module.defs().size(), slices.defs().size());
        assertEquals(module.behaviors().size(), slices.behaviors().size());
        assertEquals(module.fns().size(), slices.fns().size());
        for (Ast.Def def : module.defs()) {
            assertTrue(slices.defs().get(def.name()).contains("data " + def.name()),
                    slices.defs().get(def.name()));
        }
    }

    @Test
    void aDeclarationComesBackAsItWasWritten() {
        CstFrontend.Slices slices = CstFrontend.parseWithSlices("""
                module shared.money exposing ( Amount )
                import String ( length )

                // what a payment is worth
                data Amount = Int
                    invariant value >= 0

                behavior charge : (a: Amount) -> Amount constructs Amount
                let charge (a) = a
                """, null).slices();

        assertEquals("import String ( length )", slices.imports().get(0));
        assertEquals("""
                // what a payment is worth
                data Amount = Int
                    invariant value >= 0""", slices.defs().get("Amount"));
        assertEquals("behavior charge : (a: Amount) -> Amount constructs Amount",
                slices.behaviors().get("charge"));
        assertEquals("let charge (a) = a", slices.fns().get("charge"));
    }
}
