package souther.compiler.query;

import souther.compiler.meta.ModulePath;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What an edit costs. A compilation kept across edits recomputes what the edit reached and nothing
 * else, which is issue #35 — not as a caching layer bolted on, but because an answer that comes out
 * the same as the one it replaces leaves everything that read it alone.
 *
 * <p>"Not recomputed" is observed as the same answer object coming back: the store hands out what it
 * kept, so a different instance means the work ran again.
 */
class IncrementalCompilationTest {

    private static final String PRICES = """
            module shop.prices exposing ( Amount )

            data Amount = Int
                invariant value >= 0
            """;

    /** Imports shop.prices, so an edit there can reach here. */
    private static final String CART = """
            module shop.cart exposing ( Total )

            import shop.prices ( Amount )

            data Total = { paid: Amount }
            """;

    /** Names nothing from the other two, so no edit there can reach here. */
    private static final String CUSTOMERS = """
            module shop.customers exposing ( Name )

            data Name = String
                invariant String.length(value) > 0
            """;

    private static Map<String, String> workspace(String prices, String cart, String customers) {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("prices.sou", prices);
        byId.put("cart.sou", cart);
        byId.put("customers.sou", customers);
        return byId;
    }

    private static Compilation started() {
        Compilation c = Compilation.ofDocuments(workspace(PRICES, CART, CUSTOMERS), Set.of(),
                ModulePath.EMPTY);
        c.answerEverything();
        assertTrue(c.db().allReports().isEmpty(), "the workspace compiles to begin with");
        return c;
    }

    /**
     * An importer names some of what a module declares, so a declaration it does not name is none of
     * its business. Reading a module's declarations as one map made every importer depend on all of
     * them, so declaring something new — which no importer can even see yet — reached every module
     * that imported anything from there.
     */
    @Test
    void declaringSomethingNewDoesNotReachAnImporterThatDoesNotNameIt() {
        Compilation c = started();
        Answer<?> cart = c.db().ask(new Output.Classes("shop.cart"));

        c.update(workspace(PRICES + """

                data Discount = Int
                """, CART, CUSTOMERS), Set.of());
        c.answerEverything();

        assertSame(cart, c.db().ask(new Output.Classes("shop.cart")),
                "shop.cart names `Amount`, and `Amount` says what it said");
    }

    /**
     * And an edit to a declaration an importer does not name leaves it alone as well — the importer
     * reads the one it named, so what the one beside it says is none of its business.
     */
    @Test
    void editingADeclarationAnImporterDoesNotNameDoesNotReachIt() {
        Compilation c = started();
        Answer<?> cart = c.db().ask(new Output.Classes("shop.cart"));

        c.update(workspace(PRICES + """

                data Discount = { off: Int }
                """, CART, CUSTOMERS), Set.of());
        c.answerEverything();
        Answer<?> once = c.db().ask(new Output.Classes("shop.cart"));
        assertSame(cart, once, "declaring `Discount` is not shop.cart's business");

        c.update(workspace(PRICES + """

                data Discount = { off: Int, until: Date }
                """, CART, CUSTOMERS), Set.of());
        c.answerEverything();

        assertSame(once, c.db().ask(new Output.Classes("shop.cart")),
                "and neither is changing what `Discount` says");
    }

    @Test
    void anEditReachesTheModuleItWasMadeIn() {
        Compilation c = started();
        Answer<?> before = c.db().ask(new Output.Classes("shop.customers"));

        c.update(workspace(PRICES, CART, CUSTOMERS + """
                data Email = String
                    invariant matches("[^@]+@[^@]+", value)
                """), Set.of());
        c.answerEverything();

        assertNotSame(before, c.db().ask(new Output.Classes("shop.customers")));
    }

    @Test
    void anEditDoesNotReachAModuleThatNamesNothingOfIt() {
        Compilation c = started();
        Answer<?> prices = c.db().ask(new Output.Classes("shop.prices"));
        Answer<?> cart = c.db().ask(new Output.Classes("shop.cart"));

        c.update(workspace(PRICES, CART, CUSTOMERS + """
                data Email = String
                    invariant matches("[^@]+@[^@]+", value)
                """), Set.of());
        c.answerEverything();

        assertSame(prices, c.db().ask(new Output.Classes("shop.prices")));
        assertSame(cart, c.db().ask(new Output.Classes("shop.cart")));
    }

    /**
     * The boundary the whole claim rests on. An importer builds against what a module declares, so
     * changing a body it cannot see must not reach it — and that only works because a module's
     * declarations compare by what they say.
     */
    @Test
    void changingOnlyABodyDoesNotReachTheModulesThatImportIt() {
        Compilation c = started();
        Answer<?> cart = c.db().ask(new Output.Classes("shop.cart"));

        c.update(workspace(PRICES + """

                behavior twice : (n: Amount) -> Amount
                    constructs Amount
                let twice (n) = Amount(n.value * 2)
                """, CART, CUSTOMERS), Set.of());
        c.answerEverything();

        assertNotSame(prices(c), null, "the edited module is still compiled");
        assertSame(cart, c.db().ask(new Output.Classes("shop.cart")),
                "shop.cart imports a type, and the type did not change");
    }

    private static Object prices(Compilation c) {
        return c.db().ask(new Output.Classes("shop.prices")).value();
    }

    /** Two behaviors and a helper both of them call, in one module. */
    private static final String ORDERS = """
            module shop.orders exposing ( Amount )

            data Amount = Int
                invariant value >= 0

            let doubled (n) = n * 2

            behavior twice : (n: Amount) -> Amount
                constructs Amount
            let twice (n) = Amount(doubled(n.value))

            behavior thrice : (n: Amount) -> Amount
                constructs Amount
            let thrice (n) = Amount(n.value * 3)
            """;

    private static Compilation orders(String source) {
        Compilation c = Compilation.ofDocuments(Map.of("orders.sou", source), Set.of(),
                ModulePath.EMPTY);
        c.answerEverything();
        assertTrue(c.db().allReports().isEmpty(), "the module compiles to begin with");
        return c;
    }

    /** The same workspace with {@code thrice}'s body changed — an edit inside one definition, made
     * at the end of the file so nothing before it moves. */
    private static Map<String, String> thriceTimes(String factor) {
        return Map.of("orders.sou", ORDERS.replace("n.value * 3)", "n.value * " + factor + ")"));
    }

    /**
     * A body is expanded from itself and the helpers around it, so what another body in the same
     * module says is none of its business. Expanding a module's bodies as one tree made every
     * behavior depend on every other one, so editing any body in a file re-expanded all of them.
     */
    @Test
    void editingOneBodyExpandsThatBodyAndNotTheOnesBesideIt() {
        Compilation c = orders(ORDERS);
        Answer<?> twice = c.db().ask(new Bodies.LoweredBody("shop.orders", "twice"));
        Answer<?> thrice = c.db().ask(new Bodies.LoweredBody("shop.orders", "thrice"));

        c.update(thriceTimes("30"), Set.of());
        c.answerEverything();

        assertNotSame(thrice, c.db().ask(new Bodies.LoweredBody("shop.orders", "thrice")),
                "the edit is `thrice`'s, so it is expanded again");
        assertSame(twice, c.db().ask(new Bodies.LoweredBody("shop.orders", "twice")),
                "`twice` says what it said, and `thrice` is not part of it");
    }

    /**
     * And a body is checked against the behavior it implements and what the module around it means,
     * so a mistake made in another body — or its being edited at all — is none of its business.
     */
    @Test
    void editingOneBodyChecksThatBodyAndNotTheOnesBesideIt() {
        Compilation c = orders(ORDERS);
        Answer<?> twice = c.db().ask(new Bodies.CheckedBehavior("shop.orders", "twice"));
        Answer<?> thrice = c.db().ask(new Bodies.CheckedBehavior("shop.orders", "thrice"));

        c.update(thriceTimes("30"), Set.of());
        c.answerEverything();

        assertNotSame(thrice, c.db().ask(new Bodies.CheckedBehavior("shop.orders", "thrice")),
                "the edit is `thrice`'s, so it is checked again");
        assertSame(twice, c.db().ask(new Bodies.CheckedBehavior("shop.orders", "twice")),
                "`twice` is checked against `behavior twice`, which says what it said");
    }

    /**
     * A helper is expanded into the bodies that call it, so editing one reaches them. It reaches the
     * ones that do not call it as well: a body reads the module's helpers, not the helpers it calls,
     * and narrowing that is per-helper work rather than per-body work.
     */
    @Test
    void editingAHelperReachesTheBodiesItIsExpandedInto() {
        Compilation c = orders(ORDERS);
        Answer<?> twice = c.db().ask(new Bodies.LoweredBody("shop.orders", "twice"));

        c.update(Map.of("orders.sou", ORDERS.replace("let doubled (n) = n * 2",
                "let doubled (n) = n * 2 + 0")), Set.of());
        c.answerEverything();

        assertNotSame(twice, c.db().ask(new Bodies.LoweredBody("shop.orders", "twice")),
                "`twice` calls `doubled`, and `doubled` is part of what `twice` becomes");
    }

    @Test
    void changingWhatAModuleDeclaresReachesTheModulesThatImportIt() {
        Compilation c = started();
        Answer<?> cart = c.db().ask(new Output.Classes("shop.cart"));

        c.update(workspace("""
                module shop.prices exposing ( Amount )

                data Amount = Int
                    invariant value >= 1
                """, CART, CUSTOMERS), Set.of());
        c.answerEverything();

        assertNotSame(cart, c.db().ask(new Output.Classes("shop.cart")),
                "the imported type's invariant is part of what the importer builds against");
    }

    @Test
    void settingASourceToWhatItAlreadySaidCostsNothing() {
        Compilation c = started();
        Answer<?> cart = c.db().ask(new Output.Classes("shop.cart"));

        c.update(workspace(PRICES, CART, CUSTOMERS), Set.of());
        c.answerEverything();

        assertSame(cart, c.db().ask(new Output.Classes("shop.cart")));
    }

    @Test
    void aProblemThatWasFixedStopsBeingReported() {
        Compilation c = Compilation.ofDocuments(
                workspace(PRICES, CART, "module shop.customers\ndata Name = Nope\n"), Set.of(),
                ModulePath.EMPTY);
        c.answerEverything();
        assertTrue(c.db().allReports().stream().anyMatch(f -> f.report().isError()),
                "an unknown type is an error to begin with");

        c.update(workspace(PRICES, CART, CUSTOMERS), Set.of());
        c.answerEverything();

        assertTrue(c.db().allReports().isEmpty(), "the fixed error is not still listed");
    }

    @Test
    void aClosedDocumentIsForgotten() {
        Compilation c = started();
        assertTrue(c.db().isComputed(new Output.Classes("shop.customers")));

        Map<String, String> without = new LinkedHashMap<>();
        without.put("prices.sou", PRICES);
        without.put("cart.sou", CART);
        c.update(without, Set.of());
        c.answerEverything();

        assertFalse(c.db().isComputed(new Output.Classes("shop.customers")),
                "nothing will ask about a module that is not there any more");
        assertFalse(c.db().isComputed(new Front.Parsed("customers.sou")),
                "nor is its parse tree");
        assertFalse(c.db().isComputed(new Front.Text("customers.sou")),
                "nor its text");
        assertEquals(List.of("shop.prices", "shop.cart"), c.modules());
    }
}
