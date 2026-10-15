package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.DocumentShape;
import souther.compiler.check.PathReachability;
import souther.compiler.coverage.ControlPlace;
import souther.compiler.diag.SourceRendering;
import souther.compiler.partition.DecisionReading;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;
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

    /** The inner comparison asks for below 5 on the way that already holds above 10, which the
     *  reading of the decision proves no input takes. */
    private static final String MODEL = """
            module m

            data Small
            data Large

            behavior size : (n: Int) -> Small | Large
            let size (n) = if n > 10 then (if n < 5 then Small else Large) else Small
            """;

    /** The model compiled once for the class: nothing here changes it. */
    private static final Places PLACES = places();

    @Test
    void eachKindIsWrittenAsThePlaceItWasAbout() {
        Places places = PLACES;
        ObjectNode into = JSON.createObjectNode();

        AdequacyReport.reachProofsContradicted(into, "size", places.contradictions(),
                Set.of(places.way().way().rule()));

        JsonNode written = into.get("reachProofsContradicted");
        List<String> kinds = new ArrayList<>();
        written.forEach(each -> kinds.add(each.get("kind").stringValue()));
        assertEquals(List.of("arm", "comparison_outcome", "arrival", "way_no_input_takes"), kinds,
                "the places first, in the order the reading found them, the arrivals after, and"
                        + " the ways through the decision last");
        assertEquals(places.arm().arm().part(), written.get(0).get("part").intValue(),
                "an arm says which of the fork's arms");
        assertEquals(places.outcome().held(), written.get(1).get("held").booleanValue(),
                "a comparison's way says which way");
        assertFalse(written.get(2).has("held") || written.get(2).has("part"),
                "and an arrival is about the comparison and neither of its ways");
        assertEquals(written.get(1).get("construct"), written.get(2).get("construct"),
                "one comparison, written the same way both times");
        assertFalse(written.get(3).has("construct"), "a way is the conditions of several");
        assertEquals(places.way().way().rule().consulted().size(),
                written.get(3).get("way").get("conditions").size(),
                "and is written by every condition it consulted");
    }

    @Test
    void nothingTakenBackWritesNothing() {
        ObjectNode into = JSON.createObjectNode();

        AdequacyReport.reachProofsContradicted(into, "size",
                PathReachability.Answers.Contradictions.NONE, Set.of());

        assertEquals(Set.of(), Set.copyOf(into.propertyNames()), "absent, and never an empty array");
    }

    /**
     * Both places it is written are places the schema declares it, with every key it has: every
     * kind on the behavior, and on a rule the kinds a rule rests on.
     */
    @Test
    void theSchemaDeclaresItOnTheBehaviorAndOnARule() {
        Places places = PLACES;
        ObjectNode onTheBehavior = JSON.createObjectNode();
        AdequacyReport.reachProofsContradicted(onTheBehavior, "size", places.contradictions(),
                Set.of(places.way().way().rule()));
        ObjectNode onARule = JSON.createObjectNode();
        AdequacyReport.reachProofsContradicted(onARule, "size", places.contradictions(),
                Set.of());

        JsonNode document = JSON.readTree(AdequacyReport.of(places.compilation())
                .json(SourceRendering.namedByIdentity(places.compilation().texts())));
        ObjectNode behavior = (ObjectNode) document.get("modules").get(0).get("behaviors").get(0);
        behavior.set("reachProofsContradicted",
                onTheBehavior.get("reachProofsContradicted").deepCopy());
        ObjectNode rule = (ObjectNode) behavior.get("decision").get("obligations").get(0);
        rule.set("reachProofsContradicted", onARule.get("reachProofsContradicted").deepCopy());

        assertEquals(List.of(), DocumentShape.of(document).wrong(),
                "what the schema shipped beside this refuses");
    }

    /**
     * An arm and a comparison's way out of the compiled body, and the proofs about them, and a way
     * through its decision proved to be taken by no input.
     */
    private record Places(Compilation compilation, ControlPlace.Arm arm,
                          ControlPlace.Outcome outcome, DecisionReading.ImpossiblePath way) {

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
        List<DecisionReading.ImpossiblePath> impossible = compilation.db()
                .ask(new Adequacy.Decides(module)).value().get("size").read().impossible();
        if (impossible.size() != 1) {
            throw new AssertionError("the body has one way no input takes: " + impossible);
        }
        return new Places(compilation, arm, outcome, impossible.getFirst());
    }
}
