package souther.compiler.report;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
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

    private static final int ELEMENTS = 6;

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

    @Test
    void theCombinationsOfManyDecisionsAreOneSetForEachDecision() {
        Compilation compilation = Compilation.ofSource(lengthOfWhatWasKept(ELEMENTS), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        AdequacyReport report = AdequacyReport.of(compilation);
        SourceRendering rendering = SourceRendering.namedByIdentity(compilation.texts());

        List<Integer> counted = new ArrayList<>();
        JsonNode document = JsonMapper.builder().build().readTree(report.json(rendering));
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
        long made = 0;
        long notMade = 0;
        for (JsonNode each : interaction.get("obligations")) {
            if (each.get("made").asBoolean()) {
                made++;
            } else {
                notMade++;
            }
        }
        assertEquals(1, made, () -> "the one combination a row made: " + interaction);
        assertEquals(ELEMENTS, notMade, () -> "and a set for each decision: " + interaction);

        String page = report.human(rendering);
        assertTrue(page.lines().count() < 20L * ELEMENTS,
                () -> "a page about " + ELEMENTS + " decisions of " + page.lines().count()
                        + " lines");
        assertTrue(page.contains("interaction combinations 1/" + (1 << ELEMENTS)), page);
    }
}
