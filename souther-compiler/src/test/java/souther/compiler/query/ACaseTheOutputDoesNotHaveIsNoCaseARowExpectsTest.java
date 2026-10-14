package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.report.AdequacyReport;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row that expects a type the output does not have expects none of the output's cases.
 *
 * <p>The count of cases a row expects is out of the cases the output has. A row naming another type
 * is refused where it is written, and counted here as well it would make the number larger than the
 * number of cases there are — `specified 2/2` over a gap saying no row expects `Warm`.
 */
class ACaseTheOutputDoesNotHaveIsNoCaseARowExpectsTest {

    private static final String MODEL = """
            data Celsius = Int
            data Hot

            behavior label : (t: Celsius) -> Cold | Warm

            let label (t) = if t.value < 24 then Cold else Warm

            example label
                | "23 is cold" : (Celsius(23)) -> Cold
                | "40 is hot" : (Celsius(40)) -> Hot
            """;

    @Test
    void theCountIsOfTheOutputsOwnCases() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        AdequacyReport report = AdequacyReport.of(compilation);
        SourceRendering rendering = SourceRendering.namedByIdentity(compilation.texts());

        String human = report.human(rendering);
        assertTrue(human.contains("out specified 1/2  observed 1/2  verified 1/2\n"), human);
        assertTrue(human.contains("! no row expects `Warm`"), human);

        JsonNode output = JsonMapper.builder().build().readTree(report.json(rendering))
                .get("modules").get(0).get("behaviors").get(0).get("signature").get("output");
        List<String> specified = new ArrayList<>();
        output.get("specified").forEach(each -> specified.add(each.asString()));
        assertEquals(List.of("Cold"), specified, output::toString);
    }
}
