package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.query.Compilation;
import souther.compiler.query.Scopes;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;
import souther.compiler.values.AdmissibleSet;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a position admits, and whether this compiler could say so, are the same for the same rules.
 *
 * <p>Two patterns whose meet is a large machine, beside a rule naming one string. What the three of
 * them leave is that one string, and working it out costs nothing: the answer is inside what the
 * third rule names, so it is settled by asking that string of the other two.
 *
 * <p>Which is only true of a reading that has all three before it builds anything. Read as it goes,
 * the two patterns meet first wherever the author happened to write them first — a machine of some
 * ninety thousand states — and a compiler that would not build it reports the position as one it
 * could not work out. The same rules, written in another order, cost nothing at all.
 *
 * <p>So this is the same model six ways: the three rules in every order they can be written in. The
 * answer has to be the same, and so does what the reading says about itself. What is asserted is
 * both, because either alone would pass for a compiler that got the values right and the account of
 * them wrong.
 *
 * <p>Held with an ordinary allowance rather than a small one. The point is not that a large machine
 * is refused — that is {@code WhatOneAnswerIsAllowedIsSpentOnce} — but that nothing here has to
 * build one at all, whichever way round the rules arrive.
 */
class WhatARuleCostsDoesNotTurnOnWhereItIsWrittenTest {

    /**
     * Two patterns that share one string and nothing else short, and the string itself.
     *
     * <p>{@code a{300}} and {@code b{300}} make the meet large; {@code x} is what both of them
     * accept. A reading that meets the two patterns builds three hundred states against three
     * hundred, and one that reaches the written value first has a question about one string.
     */
    private static final List<String> RULES = List.of(
            "    invariant one = String.matches(\"x|a{300}\", value)",
            "    invariant two = String.matches(\"x|b{300}\", value)",
            "    invariant three = value == \"x\"");

    private static String model(List<Integer> order) {
        StringBuilder out = new StringBuilder("module demo\n\ndata Code = String\n");
        order.forEach(each -> out.append(RULES.get(each)).append('\n'));
        return out.toString();
    }

    private static AdmissibleSet admitted(List<Integer> order) {
        Compilation compilation = Compilation.ofSource(model(order), "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.diagnostics().values().stream()
                .flatMap(List::stream).map(each -> each.diagnostic().code()).toList(),
                "the model this reads has to be one somebody could write: " + order);
        Symbols symbols = Scopes.derived(compilation.db(), "demo").value();
        TypeSymbol.AtModule name = TypeSymbols.declared(new TypeKey(symbols.module(), "Code"));
        return FieldDomains.of(name,
                (Hir.Data) symbols.declarations().declaration(name.key()), symbols,
                souther.compiler.query.ReadAs.THE_COMPILATION_DOES)
                .admits(FieldDomains.THE_VALUE);
    }

    /** The same three rules in every order, and one answer between them. */
    @Test
    void everyOrderOfTheSameRulesLeavesTheSameAnswer() {
        List<List<Integer>> orders = List.of(
                List.of(0, 1, 2), List.of(0, 2, 1), List.of(1, 0, 2),
                List.of(1, 2, 0), List.of(2, 0, 1), List.of(2, 1, 0));
        AdmissibleSet first = admitted(orders.get(0));

        for (List<Integer> order : orders) {
            assertEquals(first, admitted(order),
                    "the values and the account of them, written as " + order);
        }
        assertEquals(AdmissibleSet.READ_IN_FULL, first.completeness(),
                "and every one of them is read in full, since nothing here has to be built");
    }
}
