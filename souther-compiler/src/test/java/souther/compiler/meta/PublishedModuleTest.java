package souther.compiler.meta;

import souther.compiler.Compiler;
import souther.compiler.ast.Ast;
import souther.compiler.diag.CompileException;
import souther.compiler.frontend.CstFrontend;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a module publishes into its classes comes back as the module another project needs in order
 * to import it: the same declarations, read by the same front end. Its implementation does not come
 * back, and is not needed — only the helpers an invariant calls, which are part of what a type is.
 */
class PublishedModuleTest {

    private static PublishedModule readBack(String moduleName, Map<String, byte[]> classes) {
        return PublishedModule.read(moduleName, new ClassFileDeclarations(classes::get));
    }

    @Test
    void theDeclarationsComeBackAndTheImplementationDoesNot() {
        String source = """
                module shared.money exposing ( Amount, Receipt, charge )
                import String ( length )

                data Amount = Int
                    invariant value >= 0 && withinCap(value)

                data Receipt = { paid: Amount }
                data Declined

                behavior charge : (a: Amount) -> Receipt | Declined
                    constructs Receipt, Declined
                let charge (a) = if a.value > 0 then Receipt { paid = a } else Declined

                let withinCap (n: Int) = n <= 1000000
                let unrelated (n: Int) = n + 1
                """;
        Ast.Module written = CstFrontend.parse(source, null);

        PublishedModule read = readBack("shared.money", Compiler.compile(source));

        Ast.Module back = read.module();
        assertEquals(written.name(), back.name());
        assertEquals(written.exposing(), back.exposing());
        assertEquals(names(written.defs()), names(back.defs()));
        assertEquals(List.of("charge"), back.behaviors().stream().map(Ast.BehaviorDef::name).toList());
        // the invariant needs `withinCap`, so it came; `charge` and `unrelated` are implementation
        assertEquals(List.of("withinCap"), back.fns().stream().map(Ast.FnDef::name).toList());
    }

    /** The declaration is the same declaration, invariant and all — that is what the discharge
     * analysis reads on the importing side. */
    @Test
    void anImportedTypeArrivesWithItsInvariant() {
        PublishedModule read = readBack("shared.money", Compiler.compile("""
                module shared.money exposing ( Amount )
                data Amount = Int
                    invariant value >= 0
                """));

        Ast.Data amount = (Ast.Data) read.module().defs().get(0);
        assertTrue(amount.newtype());
        assertTrue(amount.invariant().isPresent(), "the invariant did not come back");
    }

    /** No `let` comes back for any behavior, so which ones are injection targets cannot be read off
     * the module; it is carried beside it. */
    @Test
    void whichBehaviorsAreInjectedIsCarried() {
        PublishedModule read = readBack("shared.ledger", Compiler.compile("""
                module shared.ledger exposing ( Entry, record, double )
                data Entry = { amount: Int }
                behavior record : (e: Entry) -> Entry
                behavior double : (e: Entry) -> Entry constructs Entry
                let double (e) = Entry { amount = e.amount * 2 }
                """));

        assertEquals(Set.of("record"), read.injectedBehaviors());
    }

    /** A composition declares stages; what comes back is the signature it computes to, with every
     * name written out, because nothing is known here about what the reading module imports. */
    @Test
    void aCompositionComesBackAsASignature() {
        Map<String, byte[]> classes = Compiler.compileModules(List.of("""
                module shop.pricing exposing ( Cart, Priced, quote )
                data Cart = { n: Int }
                data Priced = { total: Int }
                behavior quote : (c: Cart) -> Priced constructs Priced
                let quote (c) = Priced { total = c.n }
                """, """
                module shop.checkout exposing ( Done, place, checkout : Done )
                import shop.pricing ( Cart, Priced, quote )
                data Done = { total: Int }
                behavior place : (p: Priced) -> Done constructs Done
                let place (p) = Done { total = p.total }
                behavior checkout = quote >-> place
                """));

        PublishedModule read = readBack("shop.checkout", classes);

        Ast.SpecBehavior checkout = (Ast.SpecBehavior) read.module().behaviors().stream()
                .filter(b -> b.name().equals("checkout")).findFirst().orElseThrow();
        assertEquals("shop.pricing.Cart", checkout.params().get(0).type().cases().get(0).name());
        assertEquals("shop.checkout.Done", checkout.ret().cases().get(0).name());
    }

    /** Every module of a real, layered module set survives the round trip. */
    @Test
    void everyModuleOfALayeredSetComesBack() {
        String base = """
                module shop.base exposing ( Money, Sku )
                import String ( length )
                data Money = Int
                    invariant value >= 0
                data Sku = String
                    invariant length(value) >= 1
                """;
        String catalog = """
                module shop.catalog exposing ( Item, Priced, Missing, price )
                import shop.base ( Money, Sku )
                data Item = { sku: Sku, unit: Money, count: Int }
                data Priced = { amount: Money }
                data Missing
                behavior price : (i: Item) -> Priced | Missing constructs Priced, Missing
                let price (i) = if i.count >= 1 then Priced { amount = i.unit } else Missing
                """;
        String order = """
                module shop.order exposing ( Line, Total, sum )
                import shop.catalog ( Item )
                import shop.base ( Money )
                data Line = { item: Item, count: Int }
                data Total = { amount: Money }
                behavior sum : (l: Line) -> Total constructs Total, Money
                let sum (l) = Total { amount = Money(l.item.unit.value * l.count) }
                """;
        Map<String, byte[]> classes = Compiler.compileModules(List.of(base, catalog, order));

        for (String name : List.of("shop.base", "shop.catalog", "shop.order")) {
            PublishedModule read = readBack(name, classes);
            assertEquals(name, read.module().name(), name + " did not come back");
        }
        assertEquals(names(CstFrontend.parse(order, null).defs()),
                names(readBack("shop.order", classes).module().defs()));
    }

    /** An invariant can name a helper without calling it — handing it to a combinator is the usual
     * way — and the helper is no less needed for being named that way. */
    @Test
    void aHelperAnInvariantHandsToACombinatorComesToo() {
        PublishedModule read = readBack("shop.basket", Compiler.compile("""
                module shop.basket exposing ( Basket )
                import List ( all )
                data Basket = { items: List<Int> }
                    invariant all(positive, items)
                let positive (n: Int) = n >= 1
                """));

        assertEquals(List.of("positive"),
                read.module().fns().stream().map(Ast.FnDef::name).toList());
    }

    @Test
    void aNameThatIsNotACompiledModuleReadsAsNothing() {
        assertNull(readBack("shared.money", Map.of()));
    }

    /** A module built against a boundary this compiler does not share is refused, rather than read
     * and misunderstood. */
    @Test
    void aModuleFromADifferentBoundaryIsRefused() {
        Map<String, byte[]> classes = Compiler.compile("""
                module shared.money exposing ( Amount )
                data Amount = Int
                """);
        PublishedModule.Classes stale = binaryName -> {
            PublishedModule.Declarations d =
                    new ClassFileDeclarations(classes::get).of(binaryName);
            if (d == null || d.module() == null) {
                return d;
            }
            PublishedModule.SoutherModuleView m = d.module();
            return new PublishedModule.Declarations(
                    new PublishedModule.SoutherModuleView(m.compat() + 1, "0.0.1-old", m.name(),
                            m.header(), m.imports(), m.types(), m.behaviors(), m.invariantHelpers()),
                    d.data(), d.behaviorSignature(), d.behaviorInjected());
        };

        CompileException e = assertThrows(CompileException.class,
                () -> PublishedModule.read("shared.money", stale));

        assertTrue(e.getMessage().contains("0.0.1-old"), e.getMessage());
    }

    private static List<String> names(List<Ast.Def> defs) {
        return defs.stream().map(Ast.Def::name).toList();
    }
}
