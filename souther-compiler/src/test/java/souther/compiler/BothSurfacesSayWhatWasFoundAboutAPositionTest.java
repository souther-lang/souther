package souther.compiler;

import org.junit.jupiter.api.Test;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import souther.compiler.diag.SourceNameResolver;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a report found it could not read about a position is one reading, and both surfaces write
 * from it.
 *
 * <p>They used to be assembled twice. A person reading the report was shown two lists — every rule
 * this compiler could not turn into a line, and the positions it divided no way — and the document
 * was written from the second alone. So a rule left unread at a position the axes went on to
 * measure reached one reader and stopped there, and `souther examples --strict` and a person
 * reading the same run were told different things about the same position.
 */
class BothSurfacesSayWhatWasFoundAboutAPositionTest {

    /**
     * A position the axes measure, with a rule about it the reading could not take in.
     *
     * <p>The guard divides `n`, so the position has classes. The second guard compares a form the
     * reading does not take apart, which is a rule about `n` that no line came from — and which no
     * list of positions divided no way has an entry for, because this one was divided.
     */
    private static final String MEASURED_AND_UNREAD = """
            module t

            data Low
            data Accepted = { at: Int }

            behavior classify : (n: Int) -> Accepted | Low
                constructs Accepted

            let classify (n) = {
                guard n >= 60 else Low
                guard Int.clamp(0, 100, n) > 70 else Low
                Accepted { at = n }
            }
            """;

    private static AdequacyReport reportOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        return AdequacyReport.of(compilation);
    }

    private static String humanOf(String source) {
        return reportOf(source).human(SourceNameResolver.identity());
    }

    private static JsonNode partitionOf(String source) {
        JsonNode document = JsonMapper.builder().build()
                .readTree(reportOf(source).json(SourceNameResolver.identity()));
        return document.get("modules").get(0).get("behaviors").get(0).get("partition");
    }

    /** Every position the document says something was not read about, as `position:reason`. */
    private static List<String> documentSaysNotRead(String source) {
        List<String> said = new ArrayList<>();
        partitionOf(source).get("notRead").forEach(each ->
                said.add(each.get("position").asText() + ":" + each.get("reason").asText()));
        return said;
    }

    @Test
    void aPositionOnlyTheHumanLineNamedIsInTheDocumentToo() {
        assertTrue(humanOf(MEASURED_AND_UNREAD).contains("not read: n"),
                humanOf(MEASURED_AND_UNREAD));

        assertEquals(List.of("n:unsupported_syntax"), documentSaysNotRead(MEASURED_AND_UNREAD),
                "the document says what the report said");
    }
}
