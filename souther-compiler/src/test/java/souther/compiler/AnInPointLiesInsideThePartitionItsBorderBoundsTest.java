package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.PointRole;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;
import souther.compiler.query.PartitionEvidence;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * An {@code IN} point is inside the partition its border bounds, and a row in another one is not at
 * it.
 *
 * <p>The syllabus keys the four points on a border and puts the {@code IN} point inside the
 * partition that border bounds, away from the line (ISTQB CTAL-TA v4.0 §3.1.1). Read as a side of
 * the line instead, the point runs to the end of the order — which is the same thing only where the
 * position has one line through it. With two, a row past the second line answers for the first
 * line's {@code IN} point while the partition between them has nothing in it at all.
 *
 * <p>Which leaves the two measures saying nothing between them. {@code equivalence partitions}
 * counts a partition some row reached, and a row on the border reaches it; the border's own
 * {@code IN} point is what tells that from a row inside — so when it is answered by a row in the
 * next partition along, nothing in the report is left to say it (issue #880).
 */
class AnInPointLiesInsideThePartitionItsBorderBoundsTest {

    /** Three partitions of one position: up to ten, eleven to twenty, and twenty-one up. */
    private static final String BANDS = """
            module example.bands

            data Low = { n: Int }
            data Mid = { n: Int }
            data High = { n: Int }

            behavior band : (n: Int) -> Low | Mid | High
                constructs Low, Mid, High

            let band (n) = {
                guard n > 10 else Low { n = n }
                guard n > 20 else Mid { n = n }
                High { n = n }
            }

            example band
            %s
            """;

    private static BorderAssessment borderAt(String rows, String value) {
        Compilation compilation = Compilation.ofSource(BANDS.formatted(rows), "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        Map<String, PartitionEvidence> all = compilation.db()
                .ask(new Adequacy.Coverage(compilation.modules().get(0))).value();
        assertNotNull(all, "the model under test compiles");
        return all.get("band").boundaries().stream()
                .filter(each -> each.value().equals(value)).findFirst()
                .orElseThrow(() -> new AssertionError("no border at " + value));
    }

    /**
     * A row in the partition past the next line does not answer for this line's {@code IN} point.
     *
     * <p>Thirty is in the third partition. The border at ten bounds the second, which the rows reach
     * only at its edge — so what is missing is exactly the row the {@code IN} point exists to ask
     * for, and the old reading called it covered.
     */
    @Test
    void aRowInTheNextPartitionAlongIsNotAtThisBordersInPoint() {
        BorderAssessment border = borderAt("""
                    | (5) -> Low { n = 5 }
                    | (11) -> Mid { n = 11 }
                    | (30) -> High { n = 30 }""", "10");

        assertInstanceOf(ItemAssessment.Coverage.Missed.class,
                border.owedAt(PointRole.IN).coverage(),
                "eleven is the ON point and thirty is in the partition after next");
    }

    /**
     * And a row inside that partition is.
     *
     * <p>The control. Fifteen is in the partition the border at ten bounds and is not against its
     * line, which is the whole of what the point asks for — so a reading that answered {@code Missed}
     * for every row would pass the test above and fail this one.
     */
    @Test
    void aRowInsideThatPartitionIsAtIt() {
        BorderAssessment border = borderAt("""
                    | (5) -> Low { n = 5 }
                    | (15) -> Mid { n = 15 }
                    | (30) -> High { n = 30 }""", "10");

        assertInstanceOf(ItemAssessment.Coverage.Hit.class,
                border.owedAt(PointRole.IN).coverage());
    }

    /**
     * The same on the other side: an {@code OUT} point is inside the partition the border keeps out.
     *
     * <p>The border at twenty keeps the second partition out. Five is in the first, two partitions
     * from the line, and answers for nothing here.
     */
    @Test
    void aRowTwoPartitionsOutIsNotAtThisBordersOutPoint() {
        BorderAssessment border = borderAt("""
                    | (5) -> Low { n = 5 }
                    | (30) -> High { n = 30 }""", "20");

        assertEquals(ItemAssessment.Coverage.Missed.class,
                border.owedAt(PointRole.OUT).coverage().getClass());
    }
}
