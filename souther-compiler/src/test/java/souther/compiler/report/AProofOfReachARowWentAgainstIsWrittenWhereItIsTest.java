package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.DocumentShape;
import souther.compiler.check.PathReachability;
import souther.compiler.coverage.ControlPlace;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;
import tools.jackson.databind.node.ArrayNode;
import tools.jackson.databind.node.ObjectNode;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A proof of reach a row went against is written as the place it was about, once, and under the
 * keys the schema declares for one — on the behavior, which is where the proofs are, and on a rule
 * of its decision, which names the ones it rested on the same way.
 *
 * <p>No model of this repository has a row go against one: the reading is held to that over the
 * corpora. So the places are the plan's own and the proofs taken back are put together here, which
 * is the one thing a test can do that a model cannot.
 */
class AProofOfReachARowWentAgainstIsWrittenWhereItIsTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String MODEL = """
            module m

            data Small
            data Large

            behavior size : (n: Int) -> Small | Large
            let size (n) = if n > 10 then Large else Small
            """;

    @Test
    void eachKindIsWrittenAsThePlaceItWasAbout() {
        Places places = places();
        ObjectNode into = JSON.createObjectNode();

        AdequacyReport.reachProofsContradicted(into, places.contradictions());

        JsonNode written = into.get("reachProofsContradicted");
        List<String> kinds = new ArrayList<>();
        written.forEach(each -> kinds.add(each.get("kind").stringValue()));
        assertEquals(List.of("arm", "comparison_outcome", "comparison_arrival"), kinds,
                "the places first, in the order the reading found them, and the arrivals after");
        assertEquals(places.arm().arm().part(), written.get(0).get("part").intValue(),
                "an arm says which of the fork's arms");
        assertEquals(places.outcome().held(), written.get(1).get("held").booleanValue(),
                "a comparison's way says which way");
        assertFalse(written.get(2).has("held") || written.get(2).has("part"),
                "and an arrival is about the comparison and neither of its ways");
        assertEquals(written.get(1).get("construct"), written.get(2).get("construct"),
                "one comparison, written the same way both times");
    }

    @Test
    void nothingTakenBackWritesNothing() {
        ObjectNode into = JSON.createObjectNode();

        AdequacyReport.reachProofsContradicted(into,
                PathReachability.Answers.Contradictions.NONE);

        assertEquals(Set.of(), Set.copyOf(into.propertyNames()), "absent, and never an empty array");
    }

    /** Both places it is written are places the schema declares it, with every key it has. */
    @Test
    void theSchemaDeclaresItOnTheBehaviorAndOnARule() {
        Places places = places();
        ObjectNode written = JSON.createObjectNode();
        AdequacyReport.reachProofsContradicted(written, places.contradictions());
        ArrayNode proofs = (ArrayNode) written.get("reachProofsContradicted");

        JsonNode document = JSON.readTree(AdequacyReport.of(places.compilation())
                .json(SourceRendering.namedByIdentity(places.compilation().texts())));
        ObjectNode behavior = (ObjectNode) document.get("modules").get(0).get("behaviors").get(0);
        behavior.set("reachProofsContradicted", proofs.deepCopy());
        ObjectNode rule = (ObjectNode) behavior.get("decision").get("obligations").get(0);
        rule.set("reachProofsContradicted", proofs.deepCopy());

        assertEquals(List.of(), DocumentShape.of(document).wrong(),
                "what the schema shipped beside this refuses");
    }

    /** An arm and a comparison's way out of the compiled body, and the proofs about them. */
    private record Places(Compilation compilation, ControlPlace.Arm arm,
                          ControlPlace.Outcome outcome) {

        PathReachability.Answers.Contradictions contradictions() {
            return new PathReachability.Answers.Contradictions(
                    new LinkedHashSet<>(List.of(arm, outcome)), Set.of(outcome.occurrence()));
        }
    }

    private static Places places() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String module = compilation.modules().getFirst();
        PathReachability.Answers read =
                compilation.db().ask(new Adequacy.PathReached(module)).value().get("size");
        ControlPlace.Arm arm = null;
        ControlPlace.Outcome outcome = null;
        for (ControlPlace each : read.found().keySet()) {
            if (arm == null && each instanceof ControlPlace.Arm it) {
                arm = it;
            }
            if (outcome == null && each instanceof ControlPlace.Outcome it) {
                outcome = it;
            }
        }
        if (arm == null || outcome == null) {
            throw new AssertionError("the body has an arm and a comparison: " + read.found());
        }
        return new Places(compilation, arm, outcome);
    }
}
