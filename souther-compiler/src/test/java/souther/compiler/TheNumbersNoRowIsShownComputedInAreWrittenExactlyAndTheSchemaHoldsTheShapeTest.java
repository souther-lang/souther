package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.ExactCut;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.NumberRegion;
import souther.compiler.report.AdequacyReport;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;
import tools.jackson.databind.node.ObjectNode;

import java.math.BigInteger;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The numbers a relation settles by the terms' ends and no row is shown computed in are written
 * as the runs they make, each end spelled exactly, and the schema holds the shape that is written
 * and no other.
 *
 * <p>No program the language has today reaches the state, so the writer is asked directly, of a
 * region the reading makes ({@code WhatIsClaimedOfADenseTermIsReadOffWhatEachOperationReadsTest}
 * asks that) and carries to the reason
 * ({@code ARelationLeavesAPlaceUndividedOnlyWhereTheOtherSideIsShownToReachItTest}). The word the
 * entry is under is one a compilation already writes
 * ({@code EveryPublishedReasonIsWrittenBySomeCompilationTest}), so no word is owed a model here.
 *
 * <p>The entry is held to the schema by {@link DocumentShape}, which evaluates the conditions the
 * schema states about which field goes under which word. It is not a validator of every keyword.
 */
class TheNumbersNoRowIsShownComputedInAreWrittenExactlyAndTheSchemaHoldsTheShapeTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /** An entry of a question's {@code stopped}. */
    private static final String STOP =
            "#/$defs/partition/properties/unanswered/items/properties/stopped/items";

    private static final String NOT_REACHED = "relation_not_shown_reached_at_every_value";

    private static final String OVER_A_REGION = "relation_shown_over_a_region";

    private static ObjectNode written() {
        NumberRegion numbers = NumberRegion.of(List.of(
                new NumberRegion.Run(null, ExactCut.exclusive(ExactRatio.ZERO)),
                new NumberRegion.Run(ExactCut.inclusive(new ExactRatio(
                        BigInteger.ONE, BigInteger.valueOf(3))), null)));
        ObjectNode stop = JSON.createObjectNode();
        AdequacyReport.numbersNotShownComputed(stop, numbers);
        return stop;
    }

    @Test
    void aRegionIsWrittenAsItsRunsWithEachEndSpelledExactly() {
        assertEquals(JSON.readTree("""
                {"numbersNotShownComputed": [
                  {"to": {"at": "0", "inclusive": false}},
                  {"from": {"at": "1/3", "inclusive": true}}
                ]}"""), written());
    }

    @Test
    void theEntryUnderTheWordForValuesNotShownToGetToTheRuleIsHeldToTheSchema() {
        ObjectNode stop = written().put("reason", NOT_REACHED);
        DocumentShape.Read read = DocumentShape.of(stop, STOP);
        assertEquals(List.of(), read.wrong());
        assertTrue(read.conditions() > 0, "the conditions on the field were put to the entry");
    }

    @Test
    void theSchemaWritesNoRegionOfNumbersUnderAnotherWord() {
        ObjectNode stop = written().put("reason", OVER_A_REGION);
        assertEquals(List.of(": the schema writes no `numbersNotShownComputed` here"),
                DocumentShape.of(stop, STOP).wrong());
    }

    @Test
    void theSchemaWritesNoOpenValuesUnderAnotherWord() {
        ObjectNode stop = JSON.createObjectNode().put("reason", NOT_REACHED);
        stop.putObject("leftOpen").put("atAnyLength", true);
        assertEquals(List.of(": the schema writes no `leftOpen` here"),
                DocumentShape.of(stop, STOP).wrong());
        stop.put("reason", OVER_A_REGION);
        assertEquals(List.of(), DocumentShape.of(stop, STOP).wrong());
    }

    @Test
    void anEndOfARunIsExactlyAnAtAndWhetherItIsIn() {
        ObjectNode stop = written().put("reason", NOT_REACHED);
        JsonNode runs = stop.get("numbersNotShownComputed");
        ((ObjectNode) runs.get(0).get("to")).put("approximately", 0.0);
        assertEquals(1, DocumentShape.of(stop, STOP).wrong().size());
        assertTrue(DocumentShape.of(stop, STOP).wrong().getFirst().contains("approximately"));
    }
}
