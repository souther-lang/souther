package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import souther.compiler.diag.SourceNameResolver;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A reading that could not hold what it read together says so in the document, under its own word.
 *
 * <p>Issue #877, at the surface a consumer reads. What is owed there is not that something went
 * unread — every rule about the position arrived and every one was taken in — but that the values
 * the document prints for the position may be wider than the rules leave it, so a class made out of
 * them may be one no value can be in.
 *
 * <p>Under its own {@code kind} and not among what a reading did not read. Told apart there, a
 * consumer grouping by kind counts a limit an author can go looking for a clause behind, and there
 * is no clause: the two would be one number and the sentence beside it would be false of half of
 * them.
 */
class AProductWiderThanItsRulesIsSaidInTheDocumentTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /** The witness: two invariants, each a choice reaching across both fields of one record. */
    private static final String WITNESS = """
            module demo

            data Taken

            data R = { a: String, b: String }
                invariant one = (a == "5" && b == "0") || (a == "6" && b == "1")
                invariant two = (a == "5" && b == "0") || (a == "6" && b == "0")

            behavior take : (r: R) -> Taken
            """;

    /** The same shape with each clause written at one position, which the reading holds exactly. */
    private static final String HELD = """
            module demo

            data Taken

            data R = { a: String, b: String }
                invariant one = a == "5" || a == "6"
                invariant two = b == "0"

            behavior take : (r: R) -> Taken
            """;

    /** The same, with a third position a clause of its own answers for. */
    private static final String BESIDE = """
            module demo

            data Taken

            data R = { a: String, b: String, c: Bool }
                invariant one = (a == "5" && b == "0") || (a == "6" && b == "1")
                invariant two = (a == "5" && b == "0") || (a == "6" && b == "0")
                invariant three = c == true

            behavior take : (r: R) -> Taken
            """;

    private static JsonNode behaviorOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        return JSON.readTree(AdequacyReport.of(compilation).json(SourceNameResolver.identity()))
                .get("modules").get(0).get("behaviors").get(0);
    }

    private static List<JsonNode> ofKind(String source, String kind) {
        List<JsonNode> out = new ArrayList<>();
        for (JsonNode each : behaviorOf(source).get("findings")) {
            if (each.get("kind").asString().equals(kind)) {
                out.add(each);
            }
        }
        return out;
    }

    @Test
    void thePositionsAreNamedUnderTheirOwnKind() {
        List<JsonNode> said = ofKind(WITNESS, "partition_values_not_separated");

        assertEquals(List.of("r.a", "r.b"),
                said.stream().map(each -> each.get("subject").asString()).toList(),
                "each position the product was read at is one entry");
    }

    /**
     * And nothing about it is said as a rule that went unread.
     *
     * <p>The whole of why it is its own kind. No rule is answerable for the width — it comes of the
     * clauses taken together and the limit they are read under — so an entry naming one would send
     * an author looking for a clause this compiler could not take in.
     */
    @Test
    void andNothingIsSaidAsARuleNothingRead() {
        assertEquals(List.of(), ofKind(WITNESS, "partition_not_read"),
                "no rule of this model went unread");
        for (JsonNode each : ofKind(WITNESS, "partition_values_not_separated")) {
            assertFalse(each.has("ruleId"), "no rule is answerable for it: " + each);
            assertFalse(each.has("reason"), "and what would lift it is one thing: " + each);
        }
    }

    /**
     * And a position beside them, answered by a clause of its own, is not named.
     *
     * <p>What the choice costs is the positions it reached across. Said of the reading rather than
     * of each position, "not every position is shown exact" is the only thing there is to say, and
     * every position gets it — which would name `c` for a correlation no clause about it was ever
     * part of.
     */
    @Test
    void aPositionAnsweredByAClauseOfItsOwnIsNotNamed() {
        assertEquals(List.of("r.a", "r.b"),
                ofKind(BESIDE, "partition_values_not_separated").stream()
                        .map(each -> each.get("subject").asString()).toList(),
                "c is left where its own clause put it");
    }

    /** A model whose clauses the reading holds exactly says none of this. */
    @Test
    void aReadingThatHoldsItsClausesSaysNothing() {
        assertTrue(ofKind(HELD, "partition_values_not_separated").isEmpty(),
                "each clause is written at one position, so the product is what they admit");
    }
}
