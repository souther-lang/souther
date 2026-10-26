package souther.compiler.report;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.CombinationCriterion;
import souther.compiler.query.Compilation;

import org.junit.jupiter.api.Test;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The combinations no row makes are reported by the decisions that settle them, so what a report
 * writes grows with the decisions and not with the ways they can come out.
 *
 * <p>A filter over a list of fixed length decides once for each element, and a condition as small
 * as the length of what it kept turns on every one of those decisions. With the rows making one
 * combination of them, every other is missing, and each is a combination nobody has to be told
 * apart from the rest: the ones with the first decision the other way are one set, the ones with
 * the first as it is and the second the other way are the next, and so on.
 */
class CombinationsNoRowMakesAreReportedByTheDecisionsThatSettleThemTest {

    /** The size the report first came out wrong at: one thousand and twenty-four combinations. */
    private static final int ELEMENTS = 10;

    private static String lengthOfWhatWasKept(int elements) {
        String params = IntStream.range(0, elements).mapToObj(i -> "m" + i + ": Row")
                .collect(Collectors.joining(", "));
        String names = IntStream.range(0, elements).mapToObj(i -> "m" + i)
                .collect(Collectors.joining(", "));
        String values = IntStream.range(0, elements).mapToObj(i -> "Row { days = 20 }")
                .collect(Collectors.joining(", "));
        return """
                module p
                data Row = { days: Int }
                behavior f : (%s) -> Int
                let f (%s) = List.length(List.filter(r -> r.days >= 17, [ %s ]))
                example f
                    | (%s) -> %d
                """.formatted(params, names, names, values, elements);
    }

    /**
     * Where the rows were not run with the instrumentation a combination is seen by, nothing says
     * which combinations they made, and the document is still as large as the decisions: the groups
     * are written, each with how many choices it has, and none of its choices one by one.
     */
    @Test
    void whereNothingWasReadOfTheRowsTheDocumentStillGrowsWithTheDecisions() {
        Compilation compilation = Compilation.ofSource(lengthOfWhatWasKept(ELEMENTS), "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        compilation.answerEverything();
        AdequacyReport report = AdequacyReport.of(compilation);

        String written = report.json(SourceRendering.namedByIdentity(compilation.texts()));
        assertTrue(written.length() < 1_000_000L,
                () -> "a document about " + ELEMENTS + " decisions of " + written.length()
                        + " characters");
        JsonNode interaction = JsonMapper.builder().build().readTree(written)
                .findValue("interaction");
        assertEquals(0, interaction.get("obligations").size(), "nothing was seen made");
        assertEquals(1, interaction.get("groups").size());
        JsonNode group = interaction.get("groups").get(0);
        assertEquals(1 << ELEMENTS, group.get("choices").asInt());
        assertEquals(ELEMENTS, group.get("factors").size());
        assertTrue(!group.has("unobserved"), "and nothing is said to be missing");
    }

    @Test
    void theCombinationsOfManyDecisionsAreOneSetForEachDecision() {
        Compilation compilation = Compilation.ofSource(lengthOfWhatWasKept(ELEMENTS), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        AdequacyReport report = AdequacyReport.of(compilation);
        SourceRendering rendering = SourceRendering.namedByIdentity(compilation.texts());

        List<Integer> counted = new ArrayList<>();
        String written = report.json(rendering);
        // The document grows with the decisions: an entry for each combination, each naming every
        // decision in it, came to tens of millions of characters at this size.
        assertTrue(written.length() < 1_000_000L,
                () -> "a document about " + ELEMENTS + " decisions of " + written.length()
                        + " characters");
        JsonNode document = JsonMapper.builder().build().readTree(written);
        for (JsonNode each : document.findValue("findings")) {
            if (each.get("kind").asString().equals("interaction_uncovered")) {
                counted.add(each.get("combinations").asInt());
            }
        }
        // Every combination but the one made, held once: a set for each decision, of half of
        // what is left and then half of that.
        assertEquals(IntStream.range(0, ELEMENTS).mapToObj(i -> 1 << i).toList(),
                counted.stream().sorted().toList());
        assertEquals((1 << ELEMENTS) - 1, counted.stream().mapToInt(Integer::intValue).sum());

        JsonNode interaction = document.findValue("interaction");
        assertEquals(1, interaction.get("obligations").size(),
                () -> "the one combination a row made: " + interaction);
        assertEquals(1, interaction.get("groups").size(), () -> "of one group: " + interaction);
        assertEquals(ELEMENTS, interaction.get("groups").get(0).get("unobserved").size(),
                () -> "and a set for each decision: " + interaction);

        // And the combinations of the group are told apart by their hashes. The decisions of one
        // comparison visited many times differ in the visit and in which way it came out, and a
        // hash that is linear in those leaves the combinations with as many held as each other
        // in one bucket — as many buckets as counts, where there are as many combinations as
        // subsets.
        var behavior = report.modules().getFirst().behaviors().getFirst();
        var asked = ((CombinationCriterion.Interactions) behavior.evidence().combinations())
                .measured().asked();
        assertEquals(1 << ELEMENTS, asked.ways().size());
        assertEquals(asked.ways().size(), asked.ways().keySet().stream()
                .map(each -> each.settled().hashCode()).distinct().count(),
                "the combinations of a group hash apart");

        String page = report.human(rendering);
        assertTrue(page.lines().count() < 20L * ELEMENTS,
                () -> "a page about " + ELEMENTS + " decisions of " + page.lines().count()
                        + " lines");
        assertTrue(page.contains("interaction combinations 1/" + (1 << ELEMENTS)), page);
    }
}
