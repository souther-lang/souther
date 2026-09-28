package souther.compiler;

import souther.compiler.meta.ModulePath;
import souther.compiler.partition.Generator;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A row an author writes against a value another module publishes is a baseline the search may
 * spread a further row over, the same as one written against a value of its own module.
 *
 * <p>{@code standard} is imported bare and written qualified: {@code pricing.standard} in the
 * reader's own text, {@code standard} where {@code pricing} declares it. The two spellings denote
 * one declaration, and a reading that rebuilt the declaration from the spelling it happened to be
 * looking at — the reader's qualified one, or the library's bare one — built a different value than
 * the one it started from.
 *
 * <p>{@code standard}'s computed field applies a helper, which {@code FixtureReader.raw}'s
 * interpreter has no case for at all (it only folds a literal {@code +}/{@code -}/{@code *}), so a
 * generated row that spreads over it and builds correctly only does so by running {@code standard}'s
 * own generated code through its fixture entry.
 */
class ASearchGeneratedRowSpreadsOverAnImportedBaselineTest {

    private static final String PRICING = """
            module pricing exposing ( standard, Cond, C, B, F, Amount )

            data C
            data B
            data F = C | B

            data Amount = Decimal
            data Cond = { f: F, amount: Amount }

            let bump (x: Decimal) = x + 1.0m
            let standard = Cond { f = B, amount = Amount(bump(3.0m)) }
            """;

    private static final String APP = """
            module app exposing ( calc, Out )
            import pricing ( standard, Cond, C, B, F )

            data Out = { n: Int }

            behavior calc : (c: Cond) -> Out
                constructs Out

            let calc (c) = Out { n = 0 }

            example calc
                | "base" : (standard) -> Out { n = 0 }
            """;

    @Test
    void theGeneratedRowSpreadsOverTheImportedName() {
        Compilation compilation = Compilation.ofSources(List.of(PRICING, APP), ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();

        Map<String, Adequacy.Filling> all = Adequacy.generatedOf(compilation.db(), "app");
        assertNotNull(all, "the model under test compiles");

        List<Generator.GeneratedRow> rows = all.get("calc").composed().rows();
        assertEquals(List.of("Cond { ...pricing.standard, f = C }"),
                rows.stream()
                        .map(row -> String.join(", ",
                                row.inputs().stream().map(i -> i.text()).toList()))
                        .toList());
    }
}
