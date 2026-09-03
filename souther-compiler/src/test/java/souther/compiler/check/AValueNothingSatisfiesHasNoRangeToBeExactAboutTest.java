package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Compilation;
import souther.compiler.query.Scopes;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A value nothing satisfies has no range for anything to be the whole of.
 *
 * <p>What is handed over at every position of one is unbounded both ways, which is as wide as a
 * range gets and is nothing the rules left. Said rather than let pass, because of how the question
 * is asked: whether the ranges hold a rule is asked of each rule on its own, and an emptiness
 * discharges every one of them — so a declaration nobody can build a value of came back with every
 * rule proven and its edges promised.
 *
 * <p>Which nothing downstream acted on, because a position with no values draws no lines and is
 * never asked. That is why this is written down: the answer was wrong where it happened not to
 * matter, and an answer is not made right by the reader that did not take it.
 */
class AValueNothingSatisfiesHasNoRangeToBeExactAboutTest {

    @Test
    void aDeclarationTwoOfWhoseRulesCannotBothHoldSaysSoRatherThanCertifying() {
        assertEquals(List.of("NothingIsLeft"), causesOf("""
                module example.rooms

                data Length = Int
                    invariant low = value >= 5
                    invariant high = value <= 3
                """));
    }

    /** And the same rules apart hold something, so the row above is about the pair. */
    @Test
    void eitherRuleOnItsOwnLeavesARangeAndIsCertified() {
        assertEquals(List.of(), causesOf("""
                module example.rooms

                data Length = Int
                    invariant low = value >= 5
                """));
        assertEquals(List.of(), causesOf("""
                module example.rooms

                data Length = Int
                    invariant high = value <= 3
                """));
    }

    /** The causes a declaration's projection names, by kind, in the order it files them. */
    private static List<String> causesOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Symbols symbols = Scopes.derived(compilation.db(), module).value();
        assertNotNull(symbols);
        TypeSymbol.AtModule named = TypeSymbols.declared(new TypeKey(module, "Length"));
        assertNotNull(symbols.declaredNode(named.key()), "no `Length` declared");
        FieldDomains domains = FieldDomains.of(named, RuleReadings.of(compilation, module),
                souther.compiler.query.ReadAs.THE_COMPILATION_DOES);
        return domains.projection().causes().stream()
                .map(cause -> cause.getClass().getSimpleName())
                .toList();
    }
}
