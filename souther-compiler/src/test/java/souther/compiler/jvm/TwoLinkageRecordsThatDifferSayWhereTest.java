package souther.compiler.jvm;

import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * Two records are unequal exactly where they differ under some label.
 *
 * <p>The contract a report of a module built against another version rests on: admission refuses a
 * module because two records are not equal, and the report says the first fact that moved. A pair
 * that is unequal with nothing moved would be a refusal with nothing to say — which is what a
 * projection putting meaning in where its facts stand among each other made, the fields of a type
 * trading places.
 */
class TwoLinkageRecordsThatDifferSayWhereTest {

    private static LinkageRecord record(String... labelsAndValues) {
        Map<String, String> facts = new LinkedHashMap<>();
        for (int i = 0; i < labelsAndValues.length; i += 2) {
            facts.put(labelsAndValues[i], labelsAndValues[i + 1]);
        }
        return new LinkageRecord(facts);
    }

    /** Held over every pair of a set that has each way two records can stand to each other. */
    @Test
    void unequalIsExactlyWhereSomethingMoved() {
        List<LinkageRecord> records = new ArrayList<>(List.of(
                record("a", "1", "b", "2"),
                record("b", "2", "a", "1"),
                record("a", "1", "b", "3"),
                record("a", "1"),
                record("a", "1", "b", "2", "c", "4"),
                record()));
        records.add(LinkageRecord.of(pair("left", "right")));
        records.add(LinkageRecord.of(pair("right", "left")));

        for (LinkageRecord one : records) {
            for (LinkageRecord other : records) {
                assertEquals(!one.equals(other), !one.movedIn(other).isEmpty(),
                        () -> one + " against " + other);
            }
        }
    }

    /** Where the facts stand among each other is how they are shown, and not what they say. */
    @Test
    void theOrderFactsAreListedInIsNotWhatTheySay() {
        assertEquals(record("a", "1", "b", "2"), record("b", "2", "a", "1"));
    }

    /** Two fields of one type trading places: the constructor takes them the other way round, and
     *  that is said as the layout moving. */
    @Test
    void fieldsTradingPlacesIsTheLayoutMoving() {
        LinkageRecord before = LinkageRecord.of(pair("left", "right"));
        LinkageRecord after = LinkageRecord.of(pair("right", "left"));

        assertNotEquals(before, after);
        assertEquals(List.of(new LinkageRecord.Moved("laid out as", "(left, right)",
                "(right, left)")), before.movedIn(after));
    }

    private static LinkageProjection.Data pair(String first, String second) {
        return new LinkageProjection.Data(new TypeKey("lib.c", "Pair"),
                LinkageProjection.Form.PRODUCT, true, "Llib/c/Pair;",
                List.of(new LinkageProjection.Field(first, Type.INT),
                        new LinkageProjection.Field(second, Type.INT)),
                List.of(), Optional.of(new LinkageProjection.Invocation(
                        LinkageProjection.Opcode.STATIC, "Llib/c/Pair;", "__construct",
                        "(JJ)Lsouther/runtime/Result;")));
    }

    /** Nothing written blank is a fact. */
    @Test
    void aFactHasALabelAndAValue() {
        assertThrows(IllegalArgumentException.class, () -> record("a", ""));
        assertThrows(IllegalArgumentException.class, () -> record("", "1"));
    }
}
