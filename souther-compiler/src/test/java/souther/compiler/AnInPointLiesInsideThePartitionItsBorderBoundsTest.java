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
        compilation.measure(Adequacy.Asked.fullReport());
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

        assertInstanceOf(ItemAssessment.Coverage.NoHit.class,
border.owedAt(PointRole.IN).coverage().made().orElseThrow(),
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
border.owedAt(PointRole.IN).coverage().made().orElseThrow());
    }

    /**
     * And a quantity that is not one position's own values is parted by every rule about it too.
     *
     * <p>A line over an arithmetic form divides no position, so it travels beside the partition
     * rather than on an axis — and it was built where the comparison was read, one rule at a time,
     * so a second line over the same form was invisible to the first. Nothing about the two lines
     * being over a form makes them any less two lines: a row where the form comes to ninety is past
     * the second of them, and answered for the first one's {@code IN} point.
     */
    @Test
    void aSecondLineOverOneFormBoundsTheFirstOnesInPoint() {
        Compilation compilation = Compilation.ofSource("""
                module example.form

                data Bound = Int
                    invariant value >= 0
                    invariant value <= 100

                data No = { why: Int }
                data Yes = { v: Int }
                data Result = No | Yes

                behavior f : (a: Bound, b: Bound) -> Result
                    constructs Yes, No

                let f (a, b) = {
                    guard Int.add(Int.multiply(3, a.value), Int.multiply(6, b.value)) > 48
                        else No { why = 0 }
                    guard Int.add(Int.multiply(3, a.value), Int.multiply(6, b.value)) > 60
                        else No { why = 1 }
                    Yes { v = 1 }
                }

                example f
                    | "one" : (Bound(1), Bound(1)) -> Yes { v = 1 }
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, PartitionEvidence> all = compilation.db()
                .ask(new Adequacy.Coverage(compilation.modules().get(0))).value();
        assertNotNull(all, "the model under test compiles");
        BorderAssessment first = all.get("f").boundaries().stream()
                .filter(each -> each.label().equals("3 * a + 6 * b = 48")).findFirst()
                .orElseThrow(() -> new AssertionError("no border at 48"));

        assertEquals("51 < 3 * a + 6 * b <= 60", first.against(PointRole.IN),
                "the run this line bounds stops at the next line, not at the end of the order");
    }

    /**
     * And two rules that write one quantity at two scales still bound each other.
     *
     * <p>{@code 3 * a + 6 * b > 48} and {@code a + 2 * b > 20} run the same way and draw two lines,
     * at sixteen and at twenty of what they are both a multiple of. Collected in the numbers each
     * rule carried, the two were sorted against each other as forty-eight and twenty — numbers of
     * different sizes — and the run between them was written out of one line's units and the other
     * line's number.
     */
    @Test
    void twoScalesOfOneQuantityBoundEachOther() {
        Compilation compilation = Compilation.ofSource("""
                module example.scales

                data Bound = Int
                    invariant value >= 0
                    invariant value <= 100

                data No = { why: Int }
                data Yes = { v: Int }
                data Result = No | Yes

                behavior f : (a: Bound, b: Bound) -> Result
                    constructs Yes, No

                let f (a, b) = {
                    guard Int.add(Int.multiply(3, a.value), Int.multiply(6, b.value)) > 48
                        else No { why = 0 }
                    guard Int.add(a.value, Int.multiply(2, b.value)) > 20 else No { why = 1 }
                    Yes { v = 1 }
                }

                example f
                    | "one" : (Bound(1), Bound(1)) -> No { why = 0 }
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, PartitionEvidence> all = compilation.db()
                .ask(new Adequacy.Coverage(compilation.modules().get(0))).value();
        assertNotNull(all, "the model under test compiles");

        assertEquals("51 < 3 * a + 6 * b <= 60",
                borderNamed(all, "3 * a + 6 * b = 48").against(PointRole.IN),
                "the first line's run stops at the second, said in the first's own units");
        assertEquals("21 < a + 2 * b <= 300",
                borderNamed(all, "a + 2 * b = 20").against(PointRole.IN),
                "and the second's runs on to what the form itself reaches, said in its own units");
    }

    private static BorderAssessment borderNamed(Map<String, PartitionEvidence> all, String label) {
        return all.get("f").boundaries().stream()
                .filter(each -> each.label().equals(label)).findFirst()
                .orElseThrow(() -> new AssertionError("no border " + label + " in "
                        + all.get("f").boundaries().stream().map(BorderAssessment::label).toList()));
    }

    /**
     * And a line the position can name and one it cannot bound each other.
     *
     * <p>The two are read by different producers — a line with a value on the position leaves its
     * border on the position, and one without leaves it on the quantity the rule wrote — and each
     * producer arranged what it could see. So a border at two tenths ran past a line at a third,
     * and the border at the third ran past two tenths in the other direction and asked for a row
     * anywhere at all.
     *
     * <p>A quantity is arranged once. Which producer a border came from is a fact about how the
     * rule was written, and the runs either side of it are a fact about the position.
     */
    @Test
    void aLineThePositionCanNameAndOneItCannotBoundEachOther() {
        Compilation compilation = Compilation.ofSource("""
                module example.mixed

                data No = { why: Int }
                data Yes = { v: Int }
                data Result = No | Yes

                behavior f : (n: Decimal) -> Result
                    constructs Yes, No

                let f (n) = {
                    guard n > 0.2m else No { why = 0 }
                    guard 3m * n > 1m else No { why = 1 }
                    Yes { v = 1 }
                }

                example f
                    | "low" : (0.1m) -> No { why = 0 }
                    | "high" : (0.5m) -> Yes { v = 1 }
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, PartitionEvidence> all = compilation.db()
                .ask(new Adequacy.Coverage(compilation.modules().get(0))).value();
        assertNotNull(all, "the model under test compiles");

        assertEquals("0.2 < n and 3 * n <= 1", borderNamed(all, "n = 0.2").against(PointRole.IN),
                "the run above two tenths stops at the third");
        assertEquals("0.6 < 3 * n and 3 * n <= 1",
                borderNamed(all, "3 * n = 1").against(PointRole.OUT),
                "and the run below the third stops at two tenths, said in the rule's own units");
        // A tenth is below two tenths, which is a partition further out. Read without the line at
        // two tenths, the run below the third reached the end of the order and a tenth answered
        // for a point that lies between the two lines.
        assertInstanceOf(ItemAssessment.Coverage.NoHit.class,
borderNamed(all, "3 * n = 1").owedAt(PointRole.OUT).coverage().made().orElseThrow(),
                "and a row two partitions out is not at it");
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

        assertEquals(ItemAssessment.Coverage.NoHit.class,
                border.owedAt(PointRole.OUT).coverage().getClass());
    }
}
