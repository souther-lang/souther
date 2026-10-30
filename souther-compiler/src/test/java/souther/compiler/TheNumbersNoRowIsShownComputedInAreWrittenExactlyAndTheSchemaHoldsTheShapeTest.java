package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.ExactCut;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.NumberRegion;
import souther.compiler.report.AdequacyReport;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;
import tools.jackson.databind.node.ObjectNode;

import java.io.IOException;
import java.io.InputStream;
import java.math.BigInteger;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * The numbers a relation settles by the terms' ends and no row is shown computed in are written
 * as the runs they make, each end spelled exactly, and the schema holds the shape that is written.
 *
 * <p>No program the language has today reaches the state, so the writer is asked directly, of a
 * region the reading makes ({@code WhatIsClaimedOfADenseTermIsReadOffWhatEachOperationReadsTest}
 * asks that) and carries to the reason
 * ({@code ARelationLeavesAPlaceUndividedOnlyWhereTheOtherSideIsShownToReachItTest}). The word the
 * entry is under is one a compilation already writes
 * ({@code EveryPublishedReasonIsWrittenBySomeCompilationTest}), so no word is owed a model here.
 */
class TheNumbersNoRowIsShownComputedInAreWrittenExactlyAndTheSchemaHoldsTheShapeTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    @Test
    void aRegionIsWrittenAsItsRunsWithEachEndSpelledExactly() {
        NumberRegion numbers = NumberRegion.of(List.of(
                new NumberRegion.Run(null, ExactCut.exclusive(ExactRatio.ZERO)),
                new NumberRegion.Run(ExactCut.inclusive(new ExactRatio(
                        BigInteger.ONE, BigInteger.valueOf(3))), null)));
        ObjectNode stop = JSON.createObjectNode();
        AdequacyReport.numbersNotShownComputed(stop, numbers);
        assertEquals(JSON.readTree("""
                {"numbersNotShownComputed": [
                  {"to": {"at": "0", "inclusive": false}},
                  {"from": {"at": "1/3", "inclusive": true}}
                ]}"""), stop);
    }

    @Test
    void theSchemaNamesWhatIsWritten() {
        JsonNode schema = schema();
        JsonNode entry = schema.at("/$defs/partition/properties/unanswered/items/properties"
                + "/stopped/items/properties/numbersNotShownComputed");
        assertFalse(entry.isMissingNode(), "a stop's entry says where the numbers are");
        assertEquals("array", entry.get("type").asString());

        NumberRegion numbers = NumberRegion.of(List.of(new NumberRegion.Run(
                ExactCut.inclusive(ExactRatio.ONE), ExactCut.inclusive(ExactRatio.of(2)))));
        ObjectNode stop = JSON.createObjectNode();
        AdequacyReport.numbersNotShownComputed(stop, numbers);
        JsonNode run = stop.get("numbersNotShownComputed").get(0);

        JsonNode items = entry.get("items");
        assertEquals(keysOf(run), keysOf(items.get("properties")));
        assertFalse(items.has("required"), "a run with no least or no greatest leaves that end out");
        for (String end : keysOf(run)) {
            String reference = items.at("/properties/" + end + "/$ref").asString();
            JsonNode cut = SchemaReference.resolve(schema, reference);
            assertEquals(keysOf(run.get(end)), keysOf(cut.get("properties")));
            Set<String> required = new LinkedHashSet<>();
            cut.get("required").forEach(each -> required.add(each.asString()));
            assertEquals(keysOf(run.get(end)), required);
            assertEquals(JSON.readTree("false"), cut.get("additionalProperties"));
        }
    }

    private static Set<String> keysOf(JsonNode node) {
        List<String> names = new ArrayList<>();
        node.propertyNames().forEach(names::add);
        return new LinkedHashSet<>(names);
    }

    private static JsonNode schema() {
        String at = "/souther/adequacy-schema-" + AdequacyReport.SCHEMA_VERSION + ".json";
        try (InputStream in = AdequacyReport.class.getResourceAsStream(at)) {
            assertNotNull(in, at + " ships beside the compiler");
            return JSON.readTree(new String(in.readAllBytes(), StandardCharsets.UTF_8));
        } catch (IOException e) {
            throw new AssertionError(e);
        }
    }
}
