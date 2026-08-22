package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.observe.Classification;
import souther.compiler.observe.Incompleteness;
import souther.compiler.partition.AxisId;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * How many reasons a hundred rows that could not be placed come to.
 *
 * <p>One per kind per position. How many rows there were is the axis's number and it is already in
 * the report; repeating it as a reason per row would be the same fact under two names, printed side
 * by side. And the two kinds stay apart, because what an author does about them is not the same: a
 * value too large to keep goes away if the fixture is written smaller, and one that could not be
 * read does not.
 */
class OneReasonPerKindPerPositionTest {

    private static final AxisId KIND = new AxisId("submit", "request.kind");
    private static final AxisId URGENT = new AxisId("submit", "request.urgent");

    private static Classification could(Incompleteness.Code code, AxisId axis) {
        return new Classification.Unclassified(
                Incompleteness.atPosition(code, axis.behavior(), axis.term()));
    }

    @SafeVarargs
    private static Map<AxisId, Classification> row(Map.Entry<AxisId, Classification>... at) {
        Map<AxisId, Classification> out = new LinkedHashMap<>();
        for (Map.Entry<AxisId, Classification> each : at) {
            out.put(each.getKey(), each.getValue());
        }
        return out;
    }

    @SafeVarargs
    @SuppressWarnings("varargs")   // `rows` is handed straight to `List.of`, which is varargs too
    private static List<Incompleteness> of(Map<AxisId, Classification>... rows) {
        return Coverages.whyUnclassified(List.of(rows), List.of(KIND, URGENT));
    }

    @Test
    void manyRowsFailingTheSameWayAtTheSamePositionAreOneReason() {
        List<Incompleteness> why = of(
                row(Map.entry(KIND, could(Incompleteness.Code.VALUE_TRUNCATED, KIND))),
                row(Map.entry(KIND, could(Incompleteness.Code.VALUE_TRUNCATED, KIND))),
                row(Map.entry(KIND, could(Incompleteness.Code.VALUE_TRUNCATED, KIND))));

        assertEquals(1, why.size(), why.toString());
        assertEquals(Incompleteness.Code.VALUE_TRUNCATED, why.get(0).code());
        assertEquals("submit/request.kind", why.get(0).subject());
    }

    @Test
    void onePositionFailingTwoWaysIsTwoReasons() {
        List<Incompleteness> why = of(
                row(Map.entry(KIND, could(Incompleteness.Code.VALUE_TRUNCATED, KIND))),
                row(Map.entry(KIND, could(Incompleteness.Code.VALUE_UNREADABLE, KIND))),
                row(Map.entry(KIND, could(Incompleteness.Code.VALUE_UNREADABLE, KIND))));

        assertEquals(List.of(Incompleteness.Code.VALUE_TRUNCATED, Incompleteness.Code.VALUE_UNREADABLE),
                why.stream().map(Incompleteness::code).toList());
        assertEquals(List.of("submit/request.kind", "submit/request.kind"),
                why.stream().map(Incompleteness::subject).toList());
    }

    @Test
    void twoPositionsFailingTheSameWayAreTwoReasons() {
        List<Incompleteness> why = of(row(
                Map.entry(KIND, could(Incompleteness.Code.VALUE_UNREADABLE, KIND)),
                Map.entry(URGENT, could(Incompleteness.Code.VALUE_UNREADABLE, URGENT))));

        assertEquals(List.of("submit/request.kind", "submit/request.urgent"),
                why.stream().map(Incompleteness::subject).toList());
    }

    /** A row that could be placed leaves nothing behind. */
    @Test
    void rowsThatWerePlacedSayNothing() {
        assertEquals(List.of(), of(row(Map.entry(KIND, Classification.in("Domestic")))));
    }
}
