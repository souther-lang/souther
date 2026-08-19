package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.query.Compilation;
import souther.compiler.query.Scopes;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * Why a line went unread is the conjunct's answer, and not the one written beside it.
 *
 * <p>A rule is read a conjunct at a time. {@code x <= 10 * 2 && x <= y} has one conjunct that draws
 * a line this compiler could not fold and one that relates two positions and draws none, and both
 * are recorded at the same position of the same rule. Asked of the rule and the position, the answer
 * was whichever the walk wrote first — so the same model said two different things about why its
 * line went unread depending on the order its conjuncts are written in.
 *
 * <p>Which is the reason the accounting asks per conjunct everywhere else: the evidence is per
 * conjunct, so what it says is too.
 */
class AReasonBelongsToTheConjunctItCameFromTest {

    /** What the reading of ends said about the line of the one clause written here. */
    private static String whyTheLineStands(String clause) {
        Compilation compilation = Compilation.ofSource("""
                module m

                data Pair = { x: Int, y: Int }
                    %s
                """.formatted(clause), "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Symbols symbols = Scopes.derived(compilation.db(), module).value();
        TypeSymbol named = TypeSymbols.declared(new TypeKey(module, "Pair"));
        Hir.Data data = (Hir.Data) symbols.declarations().declaration(named.key());

        return FieldDomains.of(named, data, symbols).accounting().values().stream()
                .flatMap(each -> each.answers().entrySet().stream())
                .filter(e -> e.getKey().obligation() == CoverageObligation.BOUNDARY)
                .map(e -> assertInstanceOf(RuleAccounting.Outcome.Unaccounted.class, e.getValue()))
                .map(e -> assertInstanceOf(RuleAccounting.Why.TheEndReadingSays.class, e.why()))
                .map(e -> e.why().getClass().getSimpleName())
                .findFirst().orElseThrow(() -> new AssertionError("the line was answered"));
    }

    /** One model, two orders, one answer: the bound this could not fold is why. */
    @Test
    void theOrderTheConjunctsAreWrittenInDoesNotDecideWhy() {
        assertEquals("UnreadComparisonForm", whyTheLineStands(
                "invariant said = x <= 10 * 2 && x <= y"));
        assertEquals("UnreadComparisonForm", whyTheLineStands(
                "invariant said = x <= y && x <= 10 * 2"),
                "and not the reason of the conjunct beside it, which relates two positions");
    }
}
