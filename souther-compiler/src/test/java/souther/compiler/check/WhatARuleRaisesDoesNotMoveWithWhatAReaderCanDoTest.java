package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.query.Scopes;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;
import souther.compiler.values.AdmissibleSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * One model, two readings of different strength, and the questions it raises are the same.
 *
 * <p>What a rule raises is the model's. A reader that can do less answers less of it — and what
 * stands unanswered is what a report is for — but the question was there to be answered either way.
 * Read the other way round, a reader gaining ground would take questions off the books, and a
 * measure of coverage would improve because this compiler improved rather than because a model was
 * written differently.
 *
 * <p><b>Said against a reading that really is weaker.</b> Two policies over one declaration: the
 * one a compilation uses, and one that holds no alternatives apart
 * ({@code ReadAs.MERGING_WHAT_A_CHOICE_LEAVES}). The clause below is a choice written at two
 * positions, which is the shape the second one falls back on — so what each position is left able
 * to hold comes back complete under the first and wider under the second, and that difference is
 * asserted here as well. Without it this would pass over two readings that did the same thing, and
 * say nothing about either.
 *
 * <p><b>Which is the check the closure cannot make.</b> That the classification names no answer is
 * said over the calls it makes ({@link WhatARuleRaisesIsComputedWithoutAnAnswerTest}); that is
 * about the code. This is about what the code came to: the same model read twice, once by a reader
 * that got further than the other.
 */
class WhatARuleRaisesDoesNotMoveWithWhatAReaderCanDoTest {

    /**
     * A choice written at two positions, which is what a reading either holds apart or merges.
     *
     * <p>Only {@code (a = "5", b = "0")} and {@code (a = "6", b = "1")} satisfy it. A reading that
     * holds the alternatives apart says so; one that merges them leaves each position with the
     * values of both alternatives and says it is wider than the rule.
     */
    private static final String SOURCE = """
            module example.either

            data P = { a: String, b: String }
                invariant one = (a == "5" && b == "0") || (a == "6" && b == "1")

            data Taken

            behavior take : (p: P) -> Taken
            """;

    @Test
    void theWeakerReadingRaisesTheSameQuestions() {
        assertEquals(read(ReadAs.THE_COMPILATION_DOES).required(),
                read(ReadAs.MERGING_WHAT_A_CHOICE_LEAVES).required(),
                "what the rule raises is the model's, and neither reading is asked about it");
    }

    /**
     * And the weaker reading is weaker, which is what makes the equality above worth asserting.
     *
     * <p>The completeness of what a position admits, and not the values themselves: both readings
     * name the same two strings at each position — what parts them is that one can say those are
     * the only ones and the other cannot, having merged the alternatives that ruled the pairs out.
     */
    @Test
    void andTheWeakerReadingReallyIsWeaker() {
        for (String field : java.util.List.of("a", "b")) {
            RuleKey at = RuleKey.of(field);
            assertInstanceOf(AdmissibleSet.Completeness.Complete.class,
                    read(ReadAs.THE_COMPILATION_DOES).admits(at).completeness(),
                    "the reading that holds the alternatives apart says what `" + field
                            + "` may hold");
            assertInstanceOf(AdmissibleSet.Completeness.Wider.class,
                    read(ReadAs.MERGING_WHAT_A_CHOICE_LEAVES).admits(at).completeness(),
                    "and the one that merges them leaves `" + field + "` wider than the rule");
        }
    }

    /** The rules of {@code P}, read under {@code policy}. */
    private static FieldDomains read(ReadingPolicy policy) {
        Compilation compilation = Compilation.ofSource(SOURCE, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Symbols symbols = Scopes.derived(compilation.db(), module).value();
        assertNotNull(symbols);
        TypeSymbol.AtModule named = TypeSymbols.declared(new TypeKey(module, "P"));
        Hir.Data data = (Hir.Data) symbols.declaredNode(named.key());
        assertNotNull(data, "no `P` declared");
        return FieldDomains.of(named, data, RuleReadings.of(compilation, module), policy);
    }
}
