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
 * A branch nothing satisfies takes everything it said with it, whatever showed it impossible.
 *
 * <p>An alternative that admits nothing is not one of the alternatives: what it left a position is
 * not something a value of this type is under, and its unread rules are rules of a branch nobody can
 * be in. That was already true of a branch two written values refuse. It has to be as true of one
 * refused by what two patterns leave between them — which nothing knows until the machines are made.
 *
 * <p>So the whole of what was read of a choice waits, and not its values alone. Held open for the
 * values while the account of what each language took in was settled, the reading answered from what
 * it happened to hold at the time: a rule the dead branch could not read was written down as a rule
 * of this declaration that went unread, and an author sent to look at it found a branch nothing
 * satisfies.
 */
class ABranchDeadOnlyByItsPatternsLeavesNothingBehindTest {

    /**
     * A branch whose two patterns share no string, beside one that names a value.
     *
     * <p>{@code a} and {@code b} accept different strings, so the left branch admits nothing — and
     * nothing says so until both machines are made and met. The {@code startsWith} beside them is a
     * rule this reading has no word for, and it is that branch's: it goes with the branch.
     */
    private static final String MODEL = """
            module demo

            data Pair = { code: String, tag: String }
                invariant r =
                    (String.matches("a", code) && String.matches("b", code)
                        && String.startsWith("q", tag))
                    || code == "c"
            """;

    private static FieldDomains read() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.answerEverything();
        assertEquals(java.util.List.of(), compilation.diagnostics().values().stream()
                .flatMap(java.util.List::stream).map(each -> each.diagnostic().code()).toList(),
                "the model this reads has to be one somebody could write");
        Symbols symbols = Scopes.derived(compilation.db(), "demo").value();
        TypeSymbol.AtModule name = TypeSymbols.declared(new TypeKey(symbols.module(), "Pair"));
        return FieldDomains.of(name,
                (Hir.Data) symbols.declarations().declaration(name.key()), symbols,
                souther.compiler.query.ReadAs.THE_COMPILATION_DOES);
    }

    /** The choice is the branch anybody can be in, which names one string. */
    @Test
    void theSurvivingBranchIsTheWholeOfWhatTheChoiceLeaves() {
        AdmissibleSet code = read().admits(RuleKey.of("code"));

        assertEquals(AdmissibleSet.READ_IN_FULL, code.completeness(),
                "the dead branch's unread rule is not this declaration's to answer for");
        assertEquals(souther.compiler.values.ValueSet.just(
                        souther.compiler.values.Value.text("c")), code.approximation(),
                "and what is left is what the branch anybody can be in says");
    }

    /**
     * And the rule is answered for, at the position only the dead branch named.
     *
     * <p>Which is where the difference shows. What each position admits comes out the same either
     * way — the dead branch admits nothing, so what it left a position adds nothing to a union —
     * and the account of who read the rule does not. Decided from what was cheap to know, the
     * branch was still standing when this was written down, and the account said a question about
     * {@code tag} was one no reading had answered. There is no branch for an author to go and look
     * at: the only rule about {@code tag} is in one nothing satisfies.
     */
    @Test
    void theRuleOfADeadBranchIsNotOneLeftUnanswered() {
        assertEquals(List.of(), unanswered(),
                "a rule of a branch nothing satisfies leaves no question behind");
    }

    /** Every question of the declaration no reading was recorded as having answered. */
    private static List<String> unanswered() {
        return read().accounting().values().stream()
                .flatMap(each -> each.answers().entrySet().stream())
                .filter(each -> each.getValue() instanceof RuleAccounting.Outcome.Unaccounted)
                .map(each -> String.valueOf(each.getKey()))
                .toList();
    }
}
