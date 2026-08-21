package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.Prepared;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Scopes;
import souther.compiler.query.Shapes;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A case the values reading kept is one it had no reason to remove, and that is not an admission.
 *
 * <p>What a position is reported as holding is an upper bound in every reading. Where the reading
 * can show it is the whole of what the rules leave, a case in it is a case the model admits; where
 * it cannot, the case may be one the rules refuse and this reading could not see them refuse. Said
 * as an admission, a `match` arm declaring the case cannot arrive is refused against a set that
 * never established it could.
 *
 * <p>Issue #877 at the seam that acts on the answer. A reading that merges what a choice leaves
 * runs to the end of every rule and still cannot hold two clauses that each relate the two
 * positions, so the product it keeps holds a pair no value of the type takes.
 *
 * <p>Held apart — which is what a compilation reads under — the same rules are answered exactly and
 * the case is refused rather than left unsettled. That answer, and every other arm this seam can
 * give, is
 * {@link EveryAnswerAPositionGivesAboutADistinctionIsOneSomeModelHereGetsTest}. What is here is the
 * one thing that is not about which arm: that a reading which kept a case for want of a reason to
 * remove it may not call it admitted.
 */
class AnUpperBoundIsNotAnAdmissionTest {

    /**
     * Only {@code (k = A, n = "0")} satisfies both clauses — a {@code k} of {@code B} is asked for
     * with {@code n = "1"} by one and with {@code n = "0"} by the other — so no value of this type
     * has {@code k = B}.
     */
    private static final String SOURCE = """
            module demo

            data A
            data B
            data K = A | B
            data Taken

            data R = { k: K, n: String }
                invariant one = (k == A && n == "0") || (k == B && n == "1")
                invariant two = (k == A && n == "0") || (k == B && n == "0")

            behavior take : (r: R) -> Taken
            """;

    private static Position positionOf(String path) {
        return positionOf(path, souther.compiler.query.ReadAs.MERGING_WHAT_A_CHOICE_LEAVES);
    }

    private static Position positionOf(String path,
                                       souther.compiler.check.ReadingPolicy policy) {
        Compilation compilation = Compilation.ofSource(SOURCE, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Prepared prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
        Map<String, Sig> sigs = compilation.db().ask(new Bodies.Signatures(module)).value();
        assertNotNull(prepared);
        Hir.SpecBehavior spec = (Hir.SpecBehavior) prepared.behaviors().stream()
                .filter(b -> b.name().equals("take")).findFirst().orElseThrow();
        Symbols symbols = Scopes.derived(compilation.db(), module).value();
        return InputDomain.of(spec, sigs.get("take"), symbols, policy).positions().stream()
                .filter(p -> p.path().toString().equals(path))
                .findFirst().orElseThrow();
    }

    private static TypeSymbol named(String name) {
        Compilation compilation = Compilation.ofSource(SOURCE, "Main");
        compilation.answerEverything();
        Symbols symbols = Scopes.derived(compilation.db(), compilation.modules().get(0)).value();
        return TypeSymbols.declared(new TypeKey(symbols.module(), name));
    }

    /**
     * The reading kept {@code B}, and may not say the model admits it.
     *
     * <p>An unsettled answer and not a refusal: the rules do refuse it, and what this reading
     * established is that it could not tell. The two are different things to act on — one is a case
     * nobody may write a row at, and one is a case nothing here settled.
     */
    @Test
    void aCaseOnlyTheProductAdmitsIsNotAdmitted() {
        Position k = positionOf("r.k");

        assertFalse(k.admissionOf(named("B")) instanceof Admits.Admitted,
                "the values are an upper bound the reading cannot show is what the rules leave");
        assertInstanceOf(Admits.Unsettled.class, k.admissionOf(named("B")));
    }

    /** And the case the rules do leave is not settled either, by the same reading. */
    @Test
    void norIsTheCaseTheRulesLeave() {
        Position k = positionOf("r.k");

        assertFalse(k.admissionOf(named("A")) instanceof Admits.Admitted,
                "one reading answers for the position, and it answers the same for both cases");
    }
}
