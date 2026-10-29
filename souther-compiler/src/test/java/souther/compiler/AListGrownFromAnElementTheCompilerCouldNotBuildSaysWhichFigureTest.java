package souther.compiler;

import org.junit.jupiter.api.Test;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A list that cannot be grown because the compiler declined to build the values of the element
 * inside its element is said to have met a figure of the compiler's, and not to have been told
 * apart from the constant by no row.
 *
 * <p>The two are different news: the second says the rows tried could not, the first that rows
 * were not tried. The body sums the lengths of the lists it holds, so only a list holding an
 * element tells it from a constant; the list held is empty, which needs none of the values of
 * {@code Huge}, and it is growing it that does.
 *
 * <p>Where the figure is carried from is {@code ElementsOfATypeTest}'s to say: the position's own
 * composing meets the same figure, so the report alone does not tell the two apart.
 */
class AListGrownFromAnElementTheCompilerCouldNotBuildSaysWhichFigureTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String MODEL = """
            module m

            data Huge = List<Bool>
                invariant List.length(value) >= 65

            behavior f : (xs: List<List<%s>>) -> Int

            let f (xs) = List.fold((acc, x) -> acc + List.length(x), 0, xs)

            example f
                | ([]) -> 0
            """;

    @Test
    void anElementTooBigToBuildLeavesTheRewriteOpenAtAFigure() {
        assertEquals(List.of("undecided: a_composing_figure_reached, no_row_answered_differently"),
                verdicts("Huge"));
    }

    @Test
    void anElementTheCompilerBuildsIsToldApart() {
        assertEquals(List.of("unnoticed: "), verdicts("Int"));
    }

    private static List<String> verdicts(String element) {
        Compilation compilation = Compilation.ofSource(MODEL.formatted(element), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), "the model compiles");
        JsonNode replacement = JSON.readTree(AdequacyReport.of(compilation)
                        .json(SourceRendering.namedByIdentity(compilation.texts())))
                .get("modules").get(0).get("behaviors").get(0).get("replacement");
        List<String> out = new ArrayList<>();
        for (JsonNode each : replacement.get("obligations")) {
            List<String> because = new ArrayList<>();
            if (each.has("undecidedBecause")) {
                each.get("undecidedBecause").forEach(word -> because.add(word.asString()));
            }
            out.add(each.get("disposition").asString() + ": " + String.join(", ", because));
        }
        return out;
    }
}
