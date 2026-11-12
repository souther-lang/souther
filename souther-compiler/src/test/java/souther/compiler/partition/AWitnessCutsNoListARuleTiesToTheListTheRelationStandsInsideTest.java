package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.ObjectMapper;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A run to an equality over a list of emails works out the total of a list of large numbers on the
 * way, which stops the run where that list holds two or more. A witness that cuts that list to
 * none gets the run past the total, and is a row only where no rule ties the list to the one the
 * equality stands inside. Where a rule says the numbers hold two wherever an email is held, every
 * run to the equality stops, and no value of either place is said to be reached; where no rule
 * ties them, the witness is a row and both are read.
 */
class AWitnessCutsNoListARuleTiesToTheListTheRelationStandsInsideTest {

    private static String model(String rule) {
        return """
                module witness

                data Big = Int invariant value >= 4611686018427387904
                data Pair = { domains: List<Big>, emails: List<String> }%s

                behavior f : (email: String, pair: Pair) -> Bool
                let f (email, pair) = {
                    let total = List.sum(List.map(d -> d.value, pair.domains))
                    List.any(own -> own == email, pair.emails) || total > 0
                }

                example f
                    | "none" : ("x", Pair { domains = [], emails = [] }) -> false
                """.formatted(rule);
    }

    /** Why each place of the equality is not read, place and reason. */
    private static List<String> notRead(String source) {
        Compilation model = Compilation.ofSource(source, "Main");
        model.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        model.answerEverything();
        assertEquals(List.of(), model.errors().stream()
                .map(e -> e.diagnostic().code()).toList(), "the model compiles");
        JsonNode report = new ObjectMapper().readTree(AdequacyReport.of(model)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
        List<String> out = new ArrayList<>();
        for (JsonNode module : report.path("modules")) {
            for (JsonNode behavior : module.path("behaviors")) {
                for (JsonNode each : behavior.path("partition").path("notRead")) {
                    String at = each.path("position").asString();
                    if (at.equals("email") || at.equals("pair.emails[*]")) {
                        out.add(at + " " + each.path("reason").asString());
                    }
                }
            }
        }
        return out;
    }

    @Test
    void noValueIsSaidReachedWhereARuleTiesTheNumbersToTheEmails() {
        List<String> said = notRead(model(
                "\n    invariant List.length(emails) == 0 || List.length(domains) >= 2"));
        assertTrue(said.contains("email relation_not_shown_reached_at_every_value")
                && said.contains("pair.emails[*] relation_not_shown_reached_at_every_value"),
                said.toString());
    }

    @Test
    void bothPlacesAreReadWhereNoRuleTiesThem() {
        List<String> said = notRead(model(""));
        assertTrue(said.stream().noneMatch(each ->
                each.endsWith("relation_not_shown_reached_at_every_value")), said.toString());
    }
}
