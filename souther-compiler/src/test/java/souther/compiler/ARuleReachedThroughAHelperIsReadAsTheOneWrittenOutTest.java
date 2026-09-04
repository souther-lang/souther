package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

import java.util.List;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule an author states by naming it is read as the rule they would have written out.
 *
 * <p>A helper call is expanded by binding each argument and reading the parameter through that
 * binding (spec §invariant-discharge-representation), so a clause stating its rule through a helper
 * is that rule under a binding. The reading that asks what a position admits and the reading that
 * asks what a construction owes both stopped at the binding: a construction the guards prove must
 * fail was refused where the rule was written out and passed in silence where the same rule reached
 * through a helper, in one module, on one model. Nothing was reported wrongly — a rule a reading
 * cannot take in widens what a position admits — but the limit was reached by using the language's
 * own way of writing a rule once and naming it twice.
 *
 * <p>The corpus below is the spellings of one rule. Every one of them says that the value is at
 * least one, so every one of them refuses the construction under {@code n <= 0} and admits the one
 * under {@code n >= 1}: what an author wrote it as decides neither.
 *
 * <p>What is <em>not</em> claimed is that a binding makes a leaf readable. Entering one says what a
 * name means and nothing about the shape standing under it, and that end is held where it can be
 * seen — {@code AClauseUnderABindingIsReadInsideItTest} fixes that the fold hands the leaf on as
 * the very node it was, so a change that widened what a leaf means instead would not pass there.
 */
class ARuleReachedThroughAHelperIsReadAsTheOneWrittenOutTest {

    /** One way of writing the rule: the helpers it needs, and the clause itself. */
    private record Spelling(String name, String helpers, String clause) {

        @Override
        public String toString() {
            return name;
        }
    }

    private static Stream<Spelling> spellings() {
        return Stream.of(
                new Spelling("written out", "", "value >= 1"),
                new Spelling("through a helper",
                        "let atLeastOne (n: Int) = n >= 1",
                        "atLeastOne(value)"),
                new Spelling("through a helper of a helper",
                        """
                        let notBelowOne (n: Int) = n >= 1
                        let atLeastOne (n: Int) = notBelowOne(n)
                        """,
                        "atLeastOne(value)"),
                new Spelling("through a helper, denied",
                        "let belowOne (n: Int) = n <= 0",
                        "Bool.not(belowOne(value))"),
                new Spelling("through a helper, denied by a truth value",
                        "let belowOne (n: Int) = n <= 0",
                        "belowOne(value) == false"),
                new Spelling("through a helper that joins two rules",
                        "let inRange (n: Int) = n >= 1 && n <= 9",
                        "inRange(value)"),
                new Spelling("through a helper the rule stands beside",
                        "let atLeastOne (n: Int) = n >= 1",
                        "atLeastOne(value) && value <= 9"),
                // A binding holding a function, with the expansion putting the body where the
                // application stood. Here because a reading that entered only the bindings an
                // argument makes would leave this one where it was.
                new Spelling("through a helper handed a helper",
                        """
                        let atLeastOne (n: Int) = n >= 1
                        let holds (p: (Int) -> Bool, n: Int) = p(n)
                        """,
                        "holds(atLeastOne, value)"),
                new Spelling("through a helper naming nothing about the value",
                        "let alwaysSo (n: Int) = 2 >= 1",
                        "alwaysSo(value) && value >= 1"));
    }

    /** The module, with {@code guard} deciding what is known where the construction stands. */
    private static String module(Spelling spelling, String guard) {
        return """
                module demo

                %s

                data Pos = Int
                    invariant %s

                data Bad

                behavior go : (n: Int) -> Pos | Bad
                    constructs Pos
                let go (n) = {
                    guard %s else Bad

                    Pos(n)
                }
                """.formatted(spelling.helpers(), spelling.clause(), guard);
    }

    @ParameterizedTest
    @MethodSource("spellings")
    void aConstructionTheGuardsRefuteIsRefused(Spelling spelling) {
        CompileException refused = assertThrows(CompileException.class,
                () -> Compiler.compile(module(spelling, "n <= 0")),
                "the value being built is one the rule rejects, however the rule was written");
        assertTrue(refused.getMessage().contains("E2010"),
                () -> "refused on the rule rather than left undischarged: " + refused.getMessage());
    }

    @ParameterizedTest
    @MethodSource("spellings")
    void aConstructionTheGuardsAllowIsBuilt(Spelling spelling) {
        assertDoesNotThrow(() -> Compiler.compile(module(spelling, "n >= 1")),
                "the rule holds of every value that reaches the construction");
    }

    /**
     * And the corpus is one rule stated many ways, rather than sources that happen to compile.
     *
     * <p>Written down because the two tests above pass on a corpus of one spelling, and what is
     * being fixed is that the spellings agree.
     */
    @Test
    void theCorpusHoldsTheRuleWrittenOutAndTheSameRuleNamed() {
        List<Spelling> corpus = spellings().toList();
        assertTrue(corpus.stream().anyMatch(one -> one.helpers().isEmpty()),
                "the rule written out is what the others are held to");
        assertTrue(corpus.stream().filter(one -> !one.helpers().isEmpty()).count() > 1,
                "and the others reach it by naming it");
    }

}
