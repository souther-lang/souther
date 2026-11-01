package souther.compiler;

import souther.compiler.partition.FixtureTemplate;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What the generator composes against a value the module states is written the way the module
 * states it, and means the value it builds written out. The meaning is what rows are told apart
 * by, so it is fixed here for the two forms the search writes: the name, and a spread over it.
 */
class ATemplateWrittenAgainstAStatedValueMeansTheValueItBuildsTest {

    private static final String A_SPREAD_OVER_A_STATED_VALUE = """
            module demo

            data C
            data B
            data F = C | B

            data Amount = Decimal
            data Cond = { f: F, amount: Amount }
            data Out = { n: Int }

            let baseline = Cond { f = B, amount = Amount(4.0m) }

            behavior calc : (c: Cond) -> Out
                constructs Out

            let calc (c) =
                match c.f with
                    | C -> Out { n = 0 }
                    | B -> Out { n = 0 }
            """;

    @Test
    void aSpreadOverAStatedValueMeansTheValueItBuilds() {
        List<FixtureTemplate> spread = composedInputs(A_SPREAD_OVER_A_STATED_VALUE).stream()
                .filter(each -> each.text().contains("...baseline")).toList();
        assertEquals(List.of("Cond { ...baseline, f = C }"),
                spread.stream().map(FixtureTemplate::text).toList());
        assertEquals(List.of("Cond { f = C, amount = Amount(4m) }"),
                spread.stream().map(FixtureTemplate::meaning).toList());
    }

    @Test
    void theNameOfAStatedValueMeansTheValueItBuilds() {
        List<FixtureTemplate> named = composedInputs(A_SPREAD_OVER_A_STATED_VALUE).stream()
                .filter(each -> each.text().equals("baseline")).toList();
        assertEquals(List.of("Cond { f = B, amount = Amount(4m) }"),
                named.stream().map(FixtureTemplate::meaning).distinct().toList());
    }

    private static List<FixtureTemplate> composedInputs(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return Adequacy.generatedOf(compilation.db(), compilation.modules().get(0))
                .get("calc").composed().rows().stream()
                .flatMap(row -> row.inputs().stream()).toList();
    }
}
