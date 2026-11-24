package souther.compiler.query;

import souther.compiler.ACompiledModel;
import souther.compiler.check.ExpandedClauseResult;
import souther.compiler.check.PublishedDeclarationResult;
import souther.compiler.meta.ModulePath;
import souther.compiler.types.TypeKey;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
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

    /**
     * A source, the codes the compiler refuses it with, the declaration asked after, and the one
     * arm both boundaries say it is in.
     */
    private record Asked(String why, String prices, List<String> refusedWith, TypeKey named,
                         String arm) {
    }

    /**
     * Both boundaries say the same arm, by the same question: whether a module writes the
     * declaration at all, asked of what the modules were parsed as.
     *
     * <p>A module the compiler stops at before working out what its declarations say, and one
     * whose imports form a ring — the case that separates the question: every answer from
     * resolution down is cut for a module in a ring, so a boundary that asked one of them would say
     * the declarations it writes are declarations nobody wrote, and a value of one would be held to
     * no rule with nothing saying so. And one whose module is refused before its {@code exposing}
     * line is read: a ring is a judgement about what a module imports and this about the module's
     * own name, cut at opposite ends of what happens to a source, so an answer to whether a
     * declaration was written is above every one of them only where it is read off the parse. A
     * name no module writes is not declared to either.
     */
    @Test
    void bothBoundariesSayWhichOfUnavailableAndNotDeclaredADeclarationIs() {
        List<Asked> cases = List.of(
                new Asked("a module that could not be read", PRICES_THAT_CANNOT_BE_READ,
                        List.of("E1022"), AMOUNT, "Unavailable"),
                new Asked("a module whose imports form a ring", PRICES_IN_A_RING,
                        List.of("E1501"), AMOUNT, "Unavailable"),
                new Asked("a module refused by its name", """
                        module souther.mine exposing ( Amount )

                        data Amount = Int
                            invariant value >= 0
                        """, List.of("E1502", "E1504"), new TypeKey("souther.mine", "Amount"),
                        "Unavailable"),
                new Asked("a name no module writes", PRICES_THAT_CANNOT_BE_READ,
                        List.of("E1022"), new TypeKey("shop.prices", "Nobody"), "NotDeclared"));
        for (Asked each : cases) {
            assertEquals(each.arm(),
                    published(each.prices(), each.refusedWith(), each.named()), each.why());
            assertEquals(each.arm(),
                    expanded(each.prices(), each.refusedWith(), each.named()), each.why());
        }
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

        assertEquals("Unavailable", published(prices, List.of("E1022", "E1506"), flag),
                "what it says is worked out where its module is, and this compiler stops there");
        assertEquals("Found", expanded(prices, List.of("E1022", "E1506"), flag),
                "and a form with no rule to write has no clauses whatever became of its module");
    }

    /** Which arm {@code named} is published in. */
    private static String published(String prices, List<String> refusedWith, TypeKey named) {
        Compilation c = compiled(prices, refusedWith);
        Object said = c.db().ask(new Shapes.MeaningOf(named)).value();
        return switch (assertInstanceOf(PublishedDeclarationResult.class, said,
                "the model says: " + c.errors())) {
            case PublishedDeclarationResult.Found _ -> "Found";
            case PublishedDeclarationResult.Unavailable _ -> "Unavailable";
            case PublishedDeclarationResult.NotDeclared _ -> "NotDeclared";
        };
    }

    /** And which arm its expanded clauses are in, named the same way so a failure compares. */
    private static String expanded(String prices, List<String> refusedWith, TypeKey named) {
        Compilation c = compiled(prices, refusedWith);
        Object said = c.db().ask(new Shapes.ClausesExpandedFor(named)).value();
        return switch (assertInstanceOf(ExpandedClauseResult.class, said,
                "the model says: " + c.errors())) {
            case ExpandedClauseResult.Found _ -> "Found";
            case ExpandedClauseResult.Unavailable _ -> "Unavailable";
            case ExpandedClauseResult.NotDeclared _ -> "NotDeclared";
        };
    }

    private static Compilation compiled(String prices, List<String> refusedWith) {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("prices.sou", prices);
        byId.put("cart.sou", CART);
        return ACompiledModel.refusedWith(refusedWith,
                Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY));
    }
}
