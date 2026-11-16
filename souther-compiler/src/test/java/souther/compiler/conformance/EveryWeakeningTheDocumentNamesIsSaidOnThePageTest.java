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
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the document says a behavior went without is said on the page under that behavior, once,
 * and nothing else is said under it, over every model of the conformance corpora.
 *
 * <p>Asked of the document and the page and not of the code that writes the page, so a surface that
 * stops saying one is a failure here whichever way it came to. The page is read in blocks, a
 * behavior's and the declarations' of its module, because a line that is true of a count of the
 * page is not one that is true of a behavior: two behaviors may share a word, and a line under one
 * is no line under the other. The words an observation gone missing writes are the reasons a page
 * prints under the behavior, and are not these.
 */
@ClosedWorldContract
class EveryWeakeningTheDocumentNamesIsSaidOnThePageTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String SAID = "? partial: ";

    @Test
    void everyBehaviorHasALineForEachWordItsDocumentCarriesAndNoOther() {
        List<String> wrong = new ArrayList<>();
        int compared = 0;
        for (ConformanceCorpus corpus : ConformanceCorpus.all()) {
            ConformanceCorpus.Analysed analysed = corpus.analyse();
            AdequacyReport report = analysed.report();
            SourceRendering rendering = new SourceRendering(corpus.names(),
                    analysed.answered().texts());
            String page = report.humanInEnglish(rendering);
            JsonNode modules = JSON.readTree(report.json(rendering)).get("modules");
            for (JsonNode module : modules) {
                PageOf block = PageOf.of(page, module.get("module").asString());
                Set<String> behaviors = new TreeSet<>();
                for (JsonNode behavior : module.get("behaviors")) {
                    String name = behavior.get("name").asString();
                    behaviors.add(name);
                    List<String> said = block.saidUnder(name);
                    List<String> carried = carried(behavior);
                    compared += carried.size();
                    if (!said.equals(carried)) {
                        wrong.add(corpus.name() + " " + module.get("module").asString() + "."
                                + name + ": the document says " + carried + " and the page "
                                + said);
                    }
                }
                for (String owner : block.ownersOfALine()) {
                    if (!behaviors.contains(owner) && !owner.equals(declarations())) {
                        wrong.add(corpus.name() + ": a line is said under " + owner
                                + ", which is no behavior of the module and not its declarations");
                    }
                }
            }
        }
        assertEquals(List.of(), wrong);
        assertTrue(compared > 0, "the corpora carry no weakening of the document's own: the sweep"
                + " found nothing to ask");
    }

    private static String declarations() {
        return Messages.get("report.declarations", Locale.ENGLISH);
    }

    /** The lines the page says for the words of one behavior's document, in the order the document
     *  has them. */
    private static List<String> carried(JsonNode behavior) {
        List<String> out = new ArrayList<>();
        JsonNode words = behavior.get("weakening");
        if (words == null) {
            return out;
        }
        for (JsonNode each : words) {
            String word = each.asString();
            if (isAWordOfTheDocument(word)) {
                out.add(Messages.get("kind.weakening." + word.replace('_', '-'), Locale.ENGLISH));
            }
        }
        return out;
    }

    private static boolean isAWordOfTheDocument(String word) {
        for (WeakeningWord each : WeakeningWord.values()) {
            if (each.name().toLowerCase(Locale.ROOT).equals(word)) {
                return true;
            }
        }
        return false;
    }

    /** One module's part of a page, cut at the lines that head something: a behavior or the
     *  declarations, two spaces in. */
    private record PageOf(List<String[]> lines) {

        static PageOf of(String page, String module) {
            List<String[]> out = new ArrayList<>();
            boolean inModule = false;
            String owner = null;
            for (String line : page.lines().toList()) {
                if (!line.startsWith(" ")) {
                    inModule = line.startsWith(module + " ");
                    owner = null;
                } else if (inModule && line.startsWith("  ") && !line.startsWith("   ")) {
                    owner = line.strip().split("\\s+")[0];
                } else if (inModule && owner != null && line.strip().startsWith(SAID)) {
                    out.add(new String[] {owner, line.strip().substring(SAID.length())});
                }
            }
            return new PageOf(out);
        }

        List<String> saidUnder(String owner) {
            return lines.stream().filter(line -> line[0].equals(owner)).map(line -> line[1])
                    .toList();
        }

        Set<String> ownersOfALine() {
            Set<String> out = new TreeSet<>();
            lines.forEach(line -> out.add(line[0]));
            return out;
        }
    }
}
