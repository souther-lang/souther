package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.BoundaryLine;
import souther.compiler.partition.PointRole;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where a behavior read a line is the whole of what the line was drawn at, and not a word off it.
 *
 * <p>A quantity runs over as many positions as it runs over. A rule relating one position to a
 * field of a sum is read once under each case of the sum, and every one of those readings writes
 * the same thing on the left — so two readings of one line share the left and are told apart by
 * what stands on the right. Named by the left alone, they arrive as one reading, and the gathering
 * of what a point came to refuses a model this compiler can otherwise read whole.
 *
 * <p>The two halves are held apart here on purpose. Two readings sharing a word are two readings;
 * two readings at one target are not two, and that is what a merge already settled.
 */
class WhereALineWasReadIsTheWholeTargetTest {

    /**
     * Two cases of one sum, each spreading the record that carries the date, and one comparison
     * against it. The walk reaches the field once under each case.
     */
    private static final String TWO_CASES = """
            module probe.twice

            data Base = { due: Date }
            data First = { ...Base }
            data Second = { ...Base }
            data Request = First | Second

            data Expired
            data Listable

            behavior check : (r: Request, today: Date) -> Listable | Expired
            let check (r, today) = {
                guard Date.daysBetween(today, r.due) >= 0 else Expired
                Listable
            }

            example check
                | "listable" : (First { due = Date("2026-08-10") }, Date("2026-08-03")) -> Listable
            """;

    /**
     * One line, read under each case of the sum, is one debt with two readings.
     *
     * <p>The left of both is {@code today}, which is what a reading named by the left could not
     * tell apart. What differs is the position the line runs to, and it is a difference the readings
     * are kept apart by: a search of one of them is about that position's own rules and values.
     */
    @Test
    void twoReadingsSharingTheLeftAreStillTwoReadings() {
        BorderObligationPointAssessment point = onePointOf(TWO_CASES);

        List<BorderObligationPointAssessment.Reading> readings =
                List.copyOf(point.met().keySet());
        assertEquals(2, readings.size(),
                () -> "the field is reached once under each case: " + readings);
        assertEquals(readings.get(0).target().left(), readings.get(1).target().left(),
                "both readings are of the same position on the left");
        assertNotEquals(readings.get(0).target(), readings.get(1).target(),
                "and they run to two different positions, which is what they are told apart by");
        assertNotEquals(readings.get(0), readings.get(1));
    }

    /**
     * A point and one of its readings are the authored line and where it was read, which is the line
     * the readings of a behavior were folded under.
     *
     * <p>What makes the fold and the gathering one equivalence rather than two that agree. The
     * point carries the authored line and the reading carries the target, so putting them back
     * together has to come out as the key the merge used — and if it did not, a reading would be
     * told apart by less than the merge folded on, whatever either half looked like on its own.
     */
    @Test
    void aPointAndAReadingOfItAreTheLineTheMergeFoldedOn() {
        for (BorderObligationPointAssessment point : pointsOf(TWO_CASES)) {
            point.met().forEach((reading, assessment) -> assertEquals(
                    BoundaryLine.of(assessment.border()),
                    new BoundaryLine(reading.target(), point.id().line(), reading.placement(),
                            reading.threshold()),
                    () -> "the point holds the authored line and the reading holds where it was"
                            + " read: " + point.point() + " at " + reading));
        }
    }

    /**
     * Two computations of one table, the bounds of one held twice over, both cut at 126 and read in
     * the two branches of one behavior.
     */
    private static final String TWO_COMPUTATIONS_CUT_AT_ONE_PLACE = """
            module probe.twice

            data N = { v: Int }
                invariant v >= 0
            data Row = { grade: Int, lowerBound: Int }
            let table: List<Row> = [ Row { grade = 1, lowerBound = 0 },
                                     Row { grade = 2, lowerBound = 63 },
                                     Row { grade = 3, lowerBound = 126 } ]
            let gradeOf (months: Int, m: Int): Int =
                List.fold((acc, r) -> if r.lowerBound * months <= m then r.grade else acc, 0, table)

            behavior f : (a: N, b: N, useTwo: Bool) -> Int

            let f (a, b, useTwo) =
                if useTwo then gradeOf(2, a.v + b.v) else gradeOf(1, a.v + b.v)

            example f
                | (N { v = 126 }, N { v = 0 }, true) -> 2
            """;

    /**
     * Readings of one point that differ in the threshold alone are two readings of it, and they put
     * back together into the line the merge kept apart.
     *
     * <p>The runs beside a line are owed once for the comparison, so the point does not tell the
     * computations apart and the readings must: otherwise the later of two replaces the earlier.
     */
    @Test
    void readingsOfOnePointThatDifferInTheThresholdAloneAreTwoReadings() {
        boolean told = false;
        for (BorderObligationPointAssessment point : pointsOf(TWO_COMPUTATIONS_CUT_AT_ONE_PLACE)) {
            List<BorderObligationPointAssessment.Reading> readings =
                    List.copyOf(point.met().keySet());
            for (int one = 0; one < readings.size(); one++) {
                for (int other = one + 1; other < readings.size(); other++) {
                    told |= readings.get(one).target().equals(readings.get(other).target())
                            && readings.get(one).placement().equals(readings.get(other).placement())
                            && !readings.get(one).threshold().equals(readings.get(other).threshold());
                }
            }
            point.met().forEach((reading, assessment) -> assertEquals(
                    BoundaryLine.of(assessment.border()),
                    new BoundaryLine(reading.target(), point.id().line(), reading.placement(),
                            reading.threshold()),
                    () -> "the reading holds where and which threshold: " + point.point()));
        }
        assertTrue(told, "a point has two readings at one target, told apart by the threshold");
    }

    /** Every point the module's lines are owed a row at. */
    private static List<BorderObligationPointAssessment> pointsOf(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        List<BorderObligationPointAssessment> points = compilation.db()
                .ask(new Adequacy.Obligations("probe.twice", new GenerationScope.Module(),
                        HowALineIsRead.VALUES_COMPOSED)).value();
        assertNotNull(points, "the model under test is read to the end");
        return points;
    }

    /** The point at the line itself, which is the one both readings meet. */
    private static BorderObligationPointAssessment onePointOf(String model) {
        List<BorderObligationPointAssessment> at = pointsOf(model).stream()
                .filter(each -> each.role() == PointRole.ON).toList();
        assertEquals(1, at.size(),
                () -> "one comparison draws one line: " + at.stream()
                        .map(each -> each.point().toString()).toList());
        return at.get(0);
    }
}
