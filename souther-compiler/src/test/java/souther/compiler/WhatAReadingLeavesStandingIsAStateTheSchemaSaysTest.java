package souther.compiler;

import org.junit.jupiter.api.Test;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import souther.compiler.diag.SourceNameResolver;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.io.InputStream;
import java.nio.charset.StandardCharsets;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a reading leaves standing is a state the schema says, not one its prose describes.
 *
 * <p>`read` carries two facts that are not the same and are not exclusive: which of a position's
 * rules nothing took in, and whether the walk reached all of them. `extent` is the word over both.
 * A description saying "present exactly where" and "never beside" is a promise a consumer written
 * against it will find broken by the first document that breaks it, since nothing refuses one; the
 * schema says it in `oneOf` instead, and this holds the emitter to the same states.
 */
class WhatAReadingLeavesStandingIsAStateTheSchemaSaysTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /** Every rule taken in, and the walk reached all of them. */
    private static final String NOTHING_STANDING = """
            module example.rooms

            data Length = Int
                invariant min = value >= 1
                invariant max = value <= 100

            behavior price : (length: Length) -> Int
            let price (length) =
                if length.value >= 50 then 1 else 2
            """;

    /** A rule that arrived and nothing took in. */
    private static final String A_RULE_UNACCOUNTED = """
            module example.rooms

            data Length = Int
                invariant min = value >= 1
                invariant square = value * value >= 4

            behavior price : (length: Length) -> Int
            let price (length) =
                if length.value >= 50 then 1 else 2
            """;

    /** Rules the walk never reached, behind an option. */
    private static final String RULES_OUT_OF_SIGHT = """
            module o

            data Assignee = String
                invariant String.length(value) >= 1

            data Issue = { assignee: Assignee? }
            data Accepted = { at: Int }

            behavior classify : (i: Issue) -> Accepted
            """;

    private static JsonNode schema() throws Exception {
        try (InputStream in =
                     AdequacyReport.class.getResourceAsStream("/souther/adequacy-schema-2.json")) {
            assertNotNull(in, "adequacy-schema-2.json ships beside the compiler");
            return JSON.readTree(new String(in.readAllBytes(), StandardCharsets.UTF_8));
        }
    }

    private static JsonNode readOf(String source, String behavior) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        JsonNode document = JSON.readTree(
                AdequacyReport.of(compilation).json(SourceNameResolver.identity()));
        for (JsonNode each : document.get("modules").get(0).get("behaviors")) {
            if (each.get("name").asString().equals(behavior)) {
                return each.get("partition").get("axes").get(0).get("read");
            }
        }
        throw new AssertionError("no behavior called " + behavior);
    }

    /**
     * The states are in the schema, and `complete` is the one where neither key is written.
     *
     * <p>Read off the schema so that a description rewritten without the constraint fails here. The
     * two keys are separate axes: nothing says a position cannot have both a rule nothing took in
     * and a subtree nothing entered, so the `partial` branch asks for at least one rather than for
     * exactly one.
     */
    @Test
    void theSchemaSaysWhichKeysEachExtentIsWrittenWith() throws Exception {
        JsonNode read = schema().get("$defs").get("partition").get("properties").get("axes")
                .get("items").get("properties").get("read");
        JsonNode states = read.get("oneOf");
        assertNotNull(states, "the states are in the schema and not only in its description");
        assertEquals(2, states.size());

        assertEquals("complete",
                states.get(0).get("properties").get("extent").get("const").asString());
        assertEquals(2, states.get(0).get("not").get("anyOf").size(),
                "complete is written with neither key");

        assertEquals("partial",
                states.get(1).get("properties").get("extent").get("const").asString());
        assertEquals(2, states.get(1).get("anyOf").size(),
                "and partial with at least one of them, either or both");

        assertTrue(read.get("properties").get("rulesNotReached").get("const").asBoolean(),
                "written only where it is so, so `false` is not a document this accepts");
        assertEquals(1, read.get("properties").get("unanswered").get("minItems").asInt(),
                "and an empty list is a position with nothing standing, which is the other state");
    }

    /** Two positions of one value, one with a rule nothing took in and one with rules out of
     *  sight. */
    private static final String BOTH_FACTS = """
            module m

            data Inner = String
                invariant String.length(value) >= 1

            data R = { n: Int, deep: Inner? }
                invariant odd = n * n >= 4

            data Ok = { at: Int }

            behavior f : (r: R) -> Ok
                constructs Ok

            let f (r) = if r.n >= 5 then Ok { at = 1 } else Ok { at = 2 }
            """;

    /**
     * The two facts are independent, and a position carries the one that is true of it.
     *
     * <p>They were arms of one type, which said they could not both be so. Nothing grounds that:
     * what a reading could not read and what a walk never reached are different facts about
     * different rules, and here they fall at two positions of one value. Whether one position can
     * carry both is not shown by this — the model and the schema allow it, and no input is known
     * that produces it.
     */
    @Test
    void aRuleNothingTookInAndRulesOutOfSightAreIndependent() {
        Compilation compilation = Compilation.ofSource(BOTH_FACTS, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        JsonNode axes = JSON.readTree(
                        AdequacyReport.of(compilation).json(SourceNameResolver.identity()))
                .get("modules").get(0).get("behaviors").get(0).get("partition").get("axes");

        JsonNode number = axes.get(0).get("read");
        assertEquals(1, number.get("unanswered").size(), number.toString());
        assertFalse(number.has("rulesNotReached"), number.toString());

        JsonNode held = axes.get(1).get("read");
        assertTrue(held.get("rulesNotReached").asBoolean(), held.toString());
        assertFalse(held.has("unanswered"), held.toString());
    }

    /** Nothing standing: `complete`, and neither key. */
    @Test
    void aPositionWithNothingStandingIsCompleteAndCarriesNeitherKey() {
        JsonNode read = readOf(NOTHING_STANDING, "price");

        assertEquals("complete", read.get("extent").asString());
        assertFalse(read.has("rulesNotReached"), read.toString());
        assertFalse(read.has("unanswered"), read.toString());
    }

    /** A rule nothing took in: `partial`, and the rules, and nothing about reach. */
    @Test
    void aRuleNothingTookInIsPartialAndNamesIt() {
        JsonNode read = readOf(A_RULE_UNACCOUNTED, "price");

        assertEquals("partial", read.get("extent").asString());
        assertFalse(read.has("rulesNotReached"), read.toString());
        assertEquals(1, read.get("unanswered").size(), read.toString());
        assertEquals("invariant Length (square)",
                read.get("unanswered").get(0).get("rule").asString());
    }

    /** Rules out of sight: `partial`, and the reach, and no rule to name. */
    @Test
    void rulesOutOfSightArePartialAndNameNoRule() {
        JsonNode read = readOf(RULES_OUT_OF_SIGHT, "classify");

        assertEquals("partial", read.get("extent").asString());
        assertTrue(read.get("rulesNotReached").asBoolean(), read.toString());
        assertFalse(read.has("unanswered"),
                "nothing was seen, so there is no rule to name: " + read);
    }
}
