package souther.compiler.check;

import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertAll;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether the rules that govern a value are short is answered from what the declarations publish,
 * and from nothing beside it.
 *
 * <p>Two ways for a declaration to say nothing, and they are opposite facts. A name nothing declares
 * carries no rule for a value to fall short of. One whose module could not be read carries whatever
 * its author wrote, and none of it came back — so a value of it is held to nothing, and what says so
 * is that the rules are short.
 *
 * <p>Which of the two it is comes from what the declaration publishes. That the walk asks nobody
 * else is not something these can see: the other place to read it is a world, and a world answers
 * about the whole compilation rather than about the module doing the reading, so the answer comes
 * out the same here either way. It is held where it can be seen, by
 * {@code TheWalkOverWhatDeclarationsPublishReadsNoWorldTest}.
 *
 * <p>The control is the same declaration in a module that does read, which is what keeps the two
 * cases below from being met by rules that are short whatever happens.
 */
class WhatIsPublishedTellsADeclarationNothingDeclaresFromOneItCouldNotReadTest {

    private static final TypeSymbol.AtModule AMOUNT =
            TypeSymbols.declared(new TypeKey("shop.prices", "Amount"));

    /** A name written in the module that declares {@code Amount}, and declared by nothing. */
    private static final TypeSymbol.AtModule NOBODY =
            TypeSymbols.declared(new TypeKey("shop.prices", "Nobody"));

    private static final String PRICES = """
            module shop.prices exposing ( Amount )

            data Amount = Int
                invariant value >= 0
            """;

    /**
     * The same module with a value defined in terms of itself.
     *
     * <p>Which is a module this compiler stops at before working out what its declarations say,
     * while leaving the declarations themselves where a reader can see there are some. Every other
     * way of writing a broken module that was tried leaves what {@code Amount} says readable — a
     * clause that does not type, a field naming no type, a body that does not check — because each
     * of those is answered for one declaration and this is answered for the module.
     */
    private static final String PRICES_THAT_CANNOT_BE_READ = PRICES + """

            let loop = loop
            """;

    /** Imports it, so its scope has the name. */
    private static final String CART = """
            module shop.cart exposing ( Basket )

            import shop.prices ( Amount )

            data Basket = { paid: Amount }
            """;

    @Test
    void aDeclarationWhoseModuleCouldNotBeReadLeavesTheRulesOfAValueShort() {
        Compilation c = compiled(PRICES_THAT_CANNOT_BE_READ);

        assertAll(
                () -> assertFalse(rulesFor(c, "shop.cart", AMOUNT).everyRuleReached(),
                        "its module could not be read, so what its author wrote did not come back"),
                () -> assertEquals(List.of(), rulesFor(c, "shop.cart", AMOUNT).reached(),
                        "and none of its rules is being held against a value"));
    }

    @Test
    void andOneNothingDeclaresLeavesNothingToBeShortOf() {
        Compilation c = compiled(PRICES_THAT_CANNOT_BE_READ);

        assertTrue(rulesFor(c, "shop.cart", NOBODY).everyRuleReached(),
                "nothing declares it, so there is no rule of it that failed to arrive");
    }

    /** And the same declaration in a module that reads is neither, which is the control. */
    @Test
    void andTheSameDeclarationInAModuleThatReadsIsNeither() {
        Compilation c = compiled(PRICES);
        PublishedRules read = rulesFor(c, "shop.cart", AMOUNT);

        assertAll(
                () -> assertEquals(1, read.reached().size(),
                        () -> "the declaration writes one rule and the walk has it: " + read),
                () -> assertTrue(read.everyRuleReached(),
                        "and nothing was left out on the way to it"));
    }

    /** What the declarations publish about {@code named}, walked from {@code module}'s reading. */
    private static PublishedRules rulesFor(Compilation c, String module, TypeSymbol.AtModule named) {
        return new Clauses(RuleReadings.of(c, module)).of(named);
    }

    /** The workspace, with {@code prices} written as the module that declares {@code Amount}. */
    private static Compilation compiled(String prices) {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("prices.sou", prices);
        byId.put("cart.sou", CART);
        Compilation c = Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
        c.answerEverything();
        return c;
    }
}
