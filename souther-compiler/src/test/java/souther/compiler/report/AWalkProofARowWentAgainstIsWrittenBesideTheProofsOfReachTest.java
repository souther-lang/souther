package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.DocumentShape;
import souther.compiler.check.PathReachability;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.WrittenOwner;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;
import tools.jackson.databind.node.ObjectNode;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A walk this compiler proved goes over one element at most, that a row then took a second
 * element of, is written down, and beside the proofs of reach and not among them.
 */
class AWalkProofARowWentAgainstIsWrittenBesideTheProofsOfReachTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final SourceConstructOrigin FOLD = SourceConstructOrigin.written(
            new WrittenOwner.Body("m", "sum"), 3, SourceConstruct.CALL);

    private static PathReachability.Answers.Contradictions contradicting(
            Set<SourceConstructOrigin> walks) {
        return new PathReachability.Answers.Contradictions(Set.of(), Set.of(), walks);
    }

    @Test
    void aWalkIsWrittenAsTheFoldTheAuthorWroteItsRewritesAreNamedBy() {
        ObjectNode into = JSON.createObjectNode();

        AdequacyReport.walkProofsContradicted(into, contradicting(Set.of(FOLD)));

        JsonNode written = into.get("walkProofsContradicted");
        assertEquals(1, written.size());
        assertEquals("m", written.get(0).get("module").stringValue());
        assertEquals("sum", written.get(0).get("definition").stringValue());
        assertEquals(3, written.get(0).get("construct").intValue());
        assertEquals(0, written.get(0).get("lowered").intValue());
    }

    @Test
    void aProofOfLengthIsNoProofOfReach() {
        ObjectNode into = JSON.createObjectNode();

        AdequacyReport.reachProofsContradicted(into, "f", contradicting(Set.of(FOLD)), Set.of());

        assertEquals(Set.of(), Set.copyOf(into.propertyNames()),
                "nothing of reach was gone against, so there is no list of it, and never an"
                        + " empty one");
    }

    @Test
    void nothingGoneAgainstWritesNothing() {
        ObjectNode into = JSON.createObjectNode();

        AdequacyReport.walkProofsContradicted(into,
                PathReachability.Answers.Contradictions.NONE);

        assertEquals(Set.of(), Set.copyOf(into.propertyNames()), "absent, and never an empty array");
    }

    /** The schema shipped beside the report declares it on the behavior, with every key it has. */
    @Test
    void theSchemaDeclaresItOnTheBehavior() {
        Compilation compilation = Compilation.ofSource("""
                module m
                behavior f : (x: Int) -> Int
                let f (x) = x
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        ObjectNode written = JSON.createObjectNode();
        AdequacyReport.walkProofsContradicted(written, contradicting(Set.of(FOLD)));

        JsonNode document = JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
        ObjectNode behavior = (ObjectNode) document.get("modules").get(0).get("behaviors").get(0);
        behavior.set("walkProofsContradicted", written.get("walkProofsContradicted").deepCopy());

        assertEquals(List.of(), DocumentShape.of(document).wrong(),
                "what the schema shipped beside this refuses");
    }
}
