package souther.compiler;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a measured model owes of the rewrites of one walk, read from the obligation list and not
 * from the page.
 *
 * <p>A page with nothing undecided on it is the same page where the rewrite was never owed, so a
 * test of a rewrite being told apart reads the obligations: both rewrites of the walk are there,
 * and neither is left open.
 */
final class WalkRewritesOwed {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private WalkRewritesOwed() {}

    /** Each rewrite of {@code walk} the model owes, as the rewrite and what became of it. */
    static List<String> of(Compilation compilation, String walk) {
        JsonNode behaviors = JSON.readTree(AdequacyReport.of(compilation)
                        .json(SourceRendering.namedByIdentity(compilation.texts())))
                .get("modules").get(0).get("behaviors");
        List<String> owed = new ArrayList<>();
        for (JsonNode behavior : behaviors) {
            JsonNode obligations = behavior.get("replacement").get("obligations");
            if (obligations == null) {
                continue;
            }
            for (JsonNode each : obligations) {
                JsonNode id = each.get("obligationId");
                if (id.has("definition") && id.get("definition").asString().equals(walk)
                        && id.get("rewrite").asString().startsWith("fold_")) {
                    owed.add(id.get("rewrite").asString() + ": "
                            + each.get("disposition").asString());
                }
            }
        }
        return owed;
    }

    /**
     * Both rewrites of {@code walk} are owed, and each is decided: a row written tells it from the
     * walk, or a row was composed that does.
     */
    static void assertToldApart(Compilation compilation, String walk) {
        List<String> owed = of(compilation, walk);
        assertEquals(List.of("fold_after_one_step", "fold_from_the_seed"),
                owed.stream().map(each -> each.substring(0, each.indexOf(':'))).toList(),
                () -> "the rewrites owed of " + walk + ": " + owed);
        assertTrue(owed.stream().noneMatch(each -> each.endsWith(": undecided")),
                () -> "left open: " + owed + "\n" + AdequacyReport.of(compilation)
                        .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts())));
    }
}
