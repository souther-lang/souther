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
