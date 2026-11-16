package souther.compiler.conformance;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.Messages;
import souther.compiler.diag.SourceRendering;
import souther.compiler.publish.WeakeningWord;
import souther.compiler.report.AdequacyReport;
import souther.test.ClosedWorldContract;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A behavior whose document names a word for what it went without has a line on the page that says
 * it, over every model of the conformance corpora.
 *
 * <p>Asked of the document and the page and not of the code that writes the page, so a surface
 * that stops saying one is a failure here whichever way it came to. The words an observation gone
 * missing writes are the reasons a page prints under the behavior, and are not these.
 */
@ClosedWorldContract
class EveryWeakeningTheDocumentNamesIsSaidOnThePageTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    @Test
    void everyWordOfTheDocumentHasALineForEachBehaviorThatCarriesIt() {
        List<String> unsaid = new ArrayList<>();
        int seen = 0;
        for (ConformanceCorpus corpus : ConformanceCorpus.all()) {
            ConformanceCorpus.Analysed analysed = corpus.analyse();
            AdequacyReport report = analysed.report();
            SourceRendering rendering = new SourceRendering(corpus.names(),
                    analysed.answered().texts());
            String page = report.humanInEnglish(rendering);
            JsonNode modules = JSON.readTree(report.json(rendering)).get("modules");
            for (WeakeningWord word : WeakeningWord.values()) {
                String key = word.name().toLowerCase(Locale.ROOT);
                long carrying = behaviors(modules)
                        .filter(behavior -> carries(behavior, key)).count();
                if (carrying == 0) {
                    continue;
                }
                seen++;
                String phrase = Messages.get("kind.weakening." + key.replace('_', '-'),
                        Locale.ENGLISH);
                long said = page.lines().filter(line -> line.endsWith(phrase)).count();
                if (said < carrying) {
                    unsaid.add(corpus.name() + ": " + key + " is carried by " + carrying
                            + " behaviors and said " + said + " times");
                }
            }
        }
        assertEquals(List.of(), unsaid);
        assertTrue(seen > 0, "the corpora carry no weakening of the document's own: the sweep"
                + " found nothing to ask");
    }

    private static Stream<JsonNode> behaviors(JsonNode modules) {
        List<JsonNode> out = new ArrayList<>();
        modules.forEach(module -> module.get("behaviors").forEach(out::add));
        return out.stream();
    }

    private static boolean carries(JsonNode behavior, String word) {
        JsonNode words = behavior.get("weakening");
        if (words == null) {
            return false;
        }
        for (JsonNode each : words) {
            if (each.asString().equals(word)) {
                return true;
            }
        }
        return false;
    }
}
