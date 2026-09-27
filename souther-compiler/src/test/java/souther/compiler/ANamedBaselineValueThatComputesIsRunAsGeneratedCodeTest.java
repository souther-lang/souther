package souther.compiler;

import souther.compiler.partition.Generator;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A row may name a module-level value whose own body computes, not only one that stands for a
 * literal or a plain construction — and once it is written that way, a further row the class
 * generation search composes may spread over the same value in turn.
 *
 * <p>{@link #aPrivateBaselineWithAComputedFieldIsNamedByARow} and {@link
 * #anAttachedFilesBaselineWithAComputedFieldIsNamedByARow} check the written row compiles and
 * passes, which a value read the old way — {@code FixtureReader.raw}, interpreting the body again —
 * already gets right for arithmetic the run time agrees with (issue #1998), so they hold whichever
 * reader answers for the named value. {@link
 * #theSearchSpreadsAGeneratedRowOverAComputedBaselineNamedByAWrittenRow} is the one that tells the
 * two apart: the class generation search composes its own row against the same value, through
 * {@code FixtureTemplate.named} and not through anything a row's own text emitted a method for —
 * which is the path {@code FixtureReader.raw} used to answer alone, and the one issue #2006 is
 * about. The baseline's computed field there applies a helper, which {@code raw}'s interpreter has
 * no case for at all (it only folds a literal `+`/`-`/`*`); a search-generated row spread over it
 * builds only because the value is read by running its own generated code.
 */
class ANamedBaselineValueThatComputesIsRunAsGeneratedCodeTest {

    @Test
    void aPrivateBaselineWithAComputedFieldIsNamedByARow() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data Amount = Decimal
                data Order = { total: Amount }
                data Accepted
                data Rejected

                let baseline = Order { total = Amount(1.5m + 2.5m) }

                behavior settle : (o: Order) -> Accepted | Rejected

                let settle (o) = if o.total == Amount(4.0m) then Accepted else Rejected

                example settle
                    | "a baseline whose total was computed" : (baseline) -> Accepted
                """));
    }

    @Test
    void anAttachedFilesBaselineWithAComputedFieldIsNamedByARow() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of("""
                module demo

                data Amount = Decimal
                data Order = { total: Amount }
                data Accepted
                data Rejected

                behavior settle : (o: Order) -> Accepted | Rejected

                let settle (o) = if o.total == Amount(4.0m) then Accepted else Rejected
                """, """
                examples for demo

                let baseline = Order { total = Amount(1.5m + 2.5m) }

                example settle
                    | "an attached baseline whose total was computed" : (baseline) -> Accepted
                """)));
    }

    private static final String A_BASELINE_A_ROW_NAMES = """
            module demo

            data C
            data B
            data F = C | B

            data Amount = Decimal
            data Cond = { f: F, amount: Amount }
            data Out = { n: Int }

            let bump (x: Decimal) = x + 1.0m
            let baseline = Cond { f = B, amount = Amount(bump(3.0m)) }

            behavior calc : (c: Cond) -> Out
                constructs Out

            let calc (c) = Out { n = 0 }

            example calc
                | "base" : (baseline) -> Out { n = 0 }
            """;

    @Test
    void theSearchSpreadsAGeneratedRowOverAComputedBaselineNamedByAWrittenRow() {
        Compilation compilation = Compilation.ofSource(A_BASELINE_A_ROW_NAMES, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, Adequacy.Filling> all =
                Adequacy.generatedOf(compilation.db(), compilation.modules().get(0));
        assertNotNull(all, "the model under test compiles");

        List<Generator.GeneratedRow> rows = all.get("calc").composed().rows();
        assertEquals(List.of("Cond { ...baseline, f = C }"),
                rows.stream()
                        .map(row -> String.join(", ",
                                row.inputs().stream().map(i -> i.text()).toList()))
                        .toList());
    }

    /** The same model, with no row ever naming {@code baseline}: the search reaches it only
     *  through its declared type, and it holds the same computed field {@code raw}'s interpreter
     *  has no case for. */
    private static final String A_BASELINE_NO_ROW_NAMES = """
            module demo

            data C
            data B
            data F = C | B

            data Amount = Decimal
            data Cond = { f: F, amount: Amount }
            data Out = { n: Int }

            let bump (x: Decimal) = x + 1.0m
            let baseline = Cond { f = B, amount = Amount(bump(3.0m)) }

            behavior calc : (c: Cond) -> Out
                constructs Out

            let calc (c) = Out { n = 0 }
            """;

    /**
     * A value no row ever names, discovered only because it is a value of a parameter's own type,
     * is a baseline the search may spread a further row over the same way a row-named one is.
     *
     * <p>{@code Adequacy.Generated.named} now only looks {@code baseline} up on {@code
     * CheckSurface.typedFixtureValues()} rather than searching for it itself, so a model with the
     * same shape and no {@code TypedFixtureValues} entry for it composes rows off the classes'
     * defaults instead — {@code Cond { f = C, amount = Amount(0m) }}, never spread over
     * {@code baseline} at all. Its body applies {@code bump}, which {@code FixtureReader.raw}'s
     * interpreter has no case for at all, so once {@code baseline} is offered as an origin again a
     * fixture reading the generated row has to run it as generated code and not by interpreting it
     * a second time.
     */
    @Test
    void theSearchSpreadsAGeneratedRowOverAComputedBaselineNoRowEverNames() {
        Compilation compilation = Compilation.ofSource(A_BASELINE_NO_ROW_NAMES, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, Adequacy.Filling> all =
                Adequacy.generatedOf(compilation.db(), compilation.modules().get(0));
        assertNotNull(all, "the model under test compiles");

        // No written row consumes baseline's own class here, so the search offers it whole as well
        // as spread with its class moved — unlike A_BASELINE_A_ROW_NAMES, where the written row
        // already covers baseline's own class and leaves the search only the moved one to fill.
        List<Generator.GeneratedRow> rows = all.get("calc").composed().rows();
        assertEquals(List.of("Cond { ...baseline, f = C }", "baseline"),
                rows.stream()
                        .map(row -> String.join(", ",
                                row.inputs().stream().map(i -> i.text()).toList()))
                        .toList());
    }
}
