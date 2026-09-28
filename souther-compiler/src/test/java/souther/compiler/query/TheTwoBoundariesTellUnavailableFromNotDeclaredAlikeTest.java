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
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * Where a declaration says nothing to either boundary, both say which of the two it is by the same
 * question.
 *
 * <p>Whether a module writes the declaration at all, asked of what the modules were parsed as. The
 * two boundaries answer different things about a declaration and are cut at different places, so
 * one of them can have an answer where the other has none; what they may not do is disagree about
 * which kind of nothing they are holding. Divided by two questions, a value would be short of its
 * rules or held to none depending on which boundary the reader met.
 *
 * <p><b>Only that division.</b> Whether either has an answer at all is each boundary's own
 * question, and the case below says so rather than leaving it to be assumed: a form with no
 * {@code invariant} to write has no clauses whatever became of its module, so the expanded side
 * answers for one whose module this compiler never got through, where the published side says what
 * it says could not be worked out. A rule holding the two to one answer everywhere would be a rule
 * about a claim neither boundary makes.
 */
class TheTwoBoundariesTellUnavailableFromNotDeclaredAlikeTest {

    private static final TypeKey AMOUNT = new TypeKey("shop.prices", "Amount");

    private static final String CART = """
            module shop.cart exposing ( Basket )

            import shop.prices ( Amount )

            data Basket = { paid: Amount }
            """;

    /** A module this compiler stops at before working out what its declarations say. */
    private static final String PRICES_THAT_CANNOT_BE_READ = """
            module shop.prices exposing ( Amount )

            data Amount = Int
                invariant value >= 0

            let loop = loop
            """;

    /** And one cut out of every answer from resolution down, while writing what it writes. */
    private static final String PRICES_IN_A_RING = """
            module shop.prices exposing ( Amount )

            import shop.cart ( Basket )

            data Amount = Int
                invariant value >= 0

            data Held = { b: Basket }
            """;

    @Test
    void aDeclarationWhoseModuleCouldNotBeReadIsUnavailableToBoth() {
        assertEquals("Unavailable", published(PRICES_THAT_CANNOT_BE_READ, AMOUNT));
        assertEquals("Unavailable", expanded(PRICES_THAT_CANNOT_BE_READ, AMOUNT));
    }

    /**
     * And one whose module's imports form a ring, which is the case that separates the question.
     *
     * <p>Every answer from resolution down is cut for a module in a ring, so a boundary that asked
     * one of them would say the declarations it writes are declarations nobody wrote — and a value
     * of one would be held to no rule, with nothing saying so.
     */
    @Test
    void andOneWhoseImportsFormARingIsUnavailableToBothAndNotUndeclared() {
        assertEquals("Unavailable", published(PRICES_IN_A_RING, AMOUNT));
        assertEquals("Unavailable", expanded(PRICES_IN_A_RING, AMOUNT));
    }

    /**
     * And one whose module is refused before its {@code exposing} line is read.
     *
     * <p>The other end of the same question. A ring is a judgement about what a module imports and
     * this is a judgement about the module's own name, and they are cut at opposite ends of what
     * happens to a source — so an answer to whether a declaration was written is above every one of
     * them only where it is read off the parse. Written here because every judgement between the
     * two is one more place an existence answer could have been taken from.
     */
    @Test
    void andOneWhoseModuleIsRefusedByItsNameIsUnavailableToBoth() {
        String prices = """
                module souther.mine exposing ( Amount )

                data Amount = Int
                    invariant value >= 0
                """;
        TypeKey mine = new TypeKey("souther.mine", "Amount");

        assertEquals("Unavailable", published(prices, mine));
        assertEquals("Unavailable", expanded(prices, mine));
    }

    @Test
    void andANameNoModuleWritesIsNotDeclaredToBoth() {
        TypeKey nobody = new TypeKey("shop.prices", "Nobody");

        assertEquals("NotDeclared", published(PRICES_THAT_CANNOT_BE_READ, nobody));
        assertEquals("NotDeclared", expanded(PRICES_THAT_CANNOT_BE_READ, nobody));
    }

    /**
     * And what the two are not held to: having an answer at the same time.
     *
     * <p>Written down as a case rather than left out, so that the rule above is not read as the
     * wider one. A unit has no {@code invariant} to write, so its clauses are answered without any
     * question of an environment to expand them in, while what it says is worked out where its
     * module is — and that module is one this compiler stops at.
     */
    @Test
    void andNeitherIsHeldToTheOtherHavingAnAnswerAtAll() {
        String prices = """
                module shop.prices exposing ( Flag )

                data Flag

                let loop = loop
                """;
        TypeKey flag = new TypeKey("shop.prices", "Flag");

        assertEquals("Unavailable", published(prices, flag),
                "what it says is worked out where its module is, and this compiler stops there");
        assertEquals("Found", expanded(prices, flag),
                "and a form with no rule to write has no clauses whatever became of its module");
    }

    /** Which arm {@code named} is published in. */
    private static String published(String prices, TypeKey named) {
        Object said = compiled(prices).db().ask(new Shapes.MeaningOf(named)).value();
        return switch (assertInstanceOf(PublishedDeclarationResult.class, said)) {
            case PublishedDeclarationResult.Found _ -> "Found";
            case PublishedDeclarationResult.Unavailable _ -> "Unavailable";
            case PublishedDeclarationResult.NotDeclared _ -> "NotDeclared";
        };
    }

    /** And which arm its expanded clauses are in, named the same way so a failure compares. */
    private static String expanded(String prices, TypeKey named) {
        Object said = compiled(prices).db().ask(new Shapes.ClausesExpandedFor(named)).value();
        return switch (assertInstanceOf(ExpandedClauseResult.class, said)) {
            case ExpandedClauseResult.Found _ -> "Found";
            case ExpandedClauseResult.Unavailable _ -> "Unavailable";
            case ExpandedClauseResult.NotDeclared _ -> "NotDeclared";
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
