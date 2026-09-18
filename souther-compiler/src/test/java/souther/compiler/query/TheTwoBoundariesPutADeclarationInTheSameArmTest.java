package souther.compiler.query;

import souther.compiler.check.ExpandedClauseResult;
import souther.compiler.check.PublishedDeclarationResult;
import souther.compiler.meta.ModulePath;
import souther.compiler.types.TypeKey;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a declaration publishes and what its clauses were expanded into are answered for or not
 * answered for together.
 *
 * <p>Two boundaries and one division. Each says found, unavailable or not declared, and each tells
 * the second from the third by asking whether the name resolves to a declaration at all. Divided by
 * two questions instead, one boundary would hold a value to rules the other says are not all there
 * — and which of them a reader met would decide whether a declaration whose module could not be
 * read left it short.
 *
 * <p>The cases are the ones a compilation reaches, measured before they were written here. What a
 * broken module costs is answered for one declaration at a time — a clause that does not type, a
 * field naming no type, a body that does not check — so none of those reaches anything but found.
 * A value defined in terms of itself is answered for the module, and stops it before its
 * declarations say anything. Imports that form a ring stop the resolution the second question is
 * itself read from, so both boundaries answer that there is no such declaration.
 *
 * <p>The control is a workspace that compiles, which is what keeps this from being met by two
 * boundaries that answer nothing for everything.
 */
class TheTwoBoundariesPutADeclarationInTheSameArmTest {

    private static final TypeKey AMOUNT = new TypeKey("shop.prices", "Amount");

    private static final String CART = """
            module shop.cart exposing ( Basket )

            import shop.prices ( Amount )

            data Basket = { paid: Amount }
            """;

    private static final String PRICES = """
            module shop.prices exposing ( Amount )

            data Amount = Int
                invariant value >= 0
            """;

    @Test
    void aDeclarationThatIsThereIsFoundByBoth() {
        assertEquals("Found", published(PRICES), "the control publishes what it says");
        assertEquals(published(PRICES), expanded(PRICES),
                "and the two boundaries put it in the same arm");
    }

    @Test
    void oneWhoseModuleCouldNotBeReadIsUnavailableToBoth() {
        String prices = PRICES + """

                let loop = loop
                """;

        assertEquals("Unavailable", published(prices),
                "the module is stopped before its declarations say anything");
        assertEquals(published(prices), expanded(prices),
                "and the two boundaries put it in the same arm");
    }

    /**
     * And one whose module's imports form a ring is not declared, to both.
     *
     * <p>Wider than a name nobody wrote, and the same width on both sides. Whether a name resolves
     * to a declaration is read from the resolution a ring stops, so the declarations of a module in
     * one are answered for as declarations there are none of.
     */
    @Test
    void oneWhoseImportsFormARingIsNotDeclaredToBoth() {
        String prices = """
                module shop.prices exposing ( Amount )

                import shop.cart ( Basket )

                data Amount = Int
                    invariant value >= 0

                data Held = { b: Basket }
                """;

        assertEquals("NotDeclared", published(prices),
                "the resolution that says whether anything declares it is the one the ring stops");
        assertEquals(published(prices), expanded(prices),
                "and the two boundaries put it in the same arm");
    }

    @Test
    void andANameNothingWroteIsNotDeclaredToBoth() {
        TypeKey nobody = new TypeKey("shop.prices", "Nobody");
        Compilation c = compiled(PRICES);

        assertEquals("NotDeclared",
                arm(c.db().ask(new Shapes.MeaningOf(nobody)).value()));
        assertEquals("NotDeclared",
                arm(c.db().ask(new Shapes.ClausesExpandedFor(nobody)).value()));
    }

    /** Which arm {@code Amount} is published in, named as the arm and not as what it holds. */
    private static String published(String prices) {
        return arm(compiled(prices).db().ask(new Shapes.MeaningOf(AMOUNT)).value());
    }

    /** And which arm its expanded clauses are in. */
    private static String expanded(String prices) {
        return arm(compiled(prices).db().ask(new Shapes.ClausesExpandedFor(AMOUNT)).value());
    }

    /**
     * The arm's own name.
     *
     * <p>Compared by name because the two answers are two types with the same three arms, and what
     * is held is that they divide alike. Compared as values they would never be equal, and a reader
     * of a failure wants to be told which arm each said rather than which record it built.
     */
    private static String arm(Object answer) {
        return switch (answer) {
            case PublishedDeclarationResult.Found _, ExpandedClauseResult.Found _ -> "Found";
            case PublishedDeclarationResult.Unavailable _, ExpandedClauseResult.Unavailable _ ->
                    "Unavailable";
            case PublishedDeclarationResult.NotDeclared _, ExpandedClauseResult.NotDeclared _ ->
                    "NotDeclared";
            default -> throw new AssertionError("neither boundary answered: " + answer);
        };
    }

    private static Compilation compiled(String prices) {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("prices.sou", prices);
        byId.put("cart.sou", CART);
        Compilation c = Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
        c.answerEverything();
        return c;
    }
}
