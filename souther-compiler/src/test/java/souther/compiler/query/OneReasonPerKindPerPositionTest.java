package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.observe.Classification;
import souther.compiler.observe.Incompleteness;
import souther.compiler.partition.Axis;
import souther.compiler.partition.AxisId;
import souther.compiler.partition.FixtureTemplate;
import souther.compiler.partition.PartitionClass;
import souther.compiler.partition.Recognition;
import souther.compiler.partition.RepresentativeSource;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * How many reasons a hundred rows that could not be placed come to.
 *
 * <p>One per kind per position. How many rows there were is the axis's number and it is already in
 * the report; repeating it as a reason per row would be the same fact under two names, printed side
 * by side. And the two kinds stay apart, because what an author does about them is not the same: a
 * value too large to keep goes away if the fixture is written smaller, and one that could not be
 * read does not.
 *
 * <p>Read off what the walk over the measures produced, and not by asking the rows about a measure
 * a caller is holding. What the rows came to at one measure is settled while they are walked, so a
 * reason is one of that entry's rather than something looked up afterwards.
 */
class OneReasonPerKindPerPositionTest {

    private static final AxisId KIND = new AxisId("submit", "request.kind");
    private static final AxisId URGENT = new AxisId("submit", "request.urgent");

    /** A measure of that number with one class, which is the least a measure can divide a position
     *  into: an axis that parts nothing is a position nothing measures and is refused. */
    private static Axis axis(AxisId id) {
        NumericTerm.ValueOf number = new NumericTerm.ValueOf(TermPath.of(id.term()));
        return new Axis(id, number,
                List.of(PartitionClass.of(id.term(), id.term(), new Recognition.Nothing(),
                                RepresentativeSource.of(List.of(FixtureTemplate.integer(1))))
                        .ofTheNumber(number)),
                List.of());
    }

    private static Classification could(Incompleteness.Code code, AxisId axis) {
        return new Classification.Unclassified(
                Incompleteness.atPosition(code, axis.behavior(), axis.term()));
    }

    /** One row, with what it said at the two measures the walk reaches in this order. */
    private static Coverages.Readings.WhereARowSat row(Classification kind, Classification urgent) {
        return new Coverages.Readings.WhereARowSat(java.util.Arrays.asList(kind, urgent));
    }

    private static List<Incompleteness> of(Coverages.Readings.WhereARowSat... rows) {
        List<Coverages.Readings.WhereARowSat> read = List.of(rows);
        List<Coverages.Readings.AxisReading> walked = new ArrayList<>();
        walked.add(Coverages.Readings.readingOf(axis(KIND), 0, read));
        walked.add(Coverages.Readings.readingOf(axis(URGENT), 1, read));
        return Coverages.Readings.reasonsIn(walked);
    }

    @Test
    void manyRowsFailingTheSameWayAtTheSamePositionAreOneReason() {
        List<Incompleteness> why = of(
                row(could(Incompleteness.Code.VALUE_TRUNCATED, KIND), null),
                row(could(Incompleteness.Code.VALUE_TRUNCATED, KIND), null),
                row(could(Incompleteness.Code.VALUE_TRUNCATED, KIND), null));

        assertEquals(1, why.size(), why.toString());
        assertEquals(Incompleteness.Code.VALUE_TRUNCATED, why.get(0).code());
        assertEquals("submit/request.kind", why.get(0).subject());
    }

    @Test
    void onePositionFailingTwoWaysIsTwoReasons() {
        List<Incompleteness> why = of(
                row(could(Incompleteness.Code.VALUE_TRUNCATED, KIND), null),
                row(could(Incompleteness.Code.VALUE_UNREADABLE, KIND), null),
                row(could(Incompleteness.Code.VALUE_UNREADABLE, KIND), null));

        assertEquals(List.of(Incompleteness.Code.VALUE_TRUNCATED, Incompleteness.Code.VALUE_UNREADABLE),
                why.stream().map(Incompleteness::code).toList());
        assertEquals(List.of("submit/request.kind", "submit/request.kind"),
                why.stream().map(Incompleteness::subject).toList());
    }

    @Test
    void twoPositionsFailingTheSameWayAreTwoReasons() {
        List<Incompleteness> why = of(row(
                could(Incompleteness.Code.VALUE_UNREADABLE, KIND),
                could(Incompleteness.Code.VALUE_UNREADABLE, URGENT)));

        assertEquals(List.of("submit/request.kind", "submit/request.urgent"),
                why.stream().map(Incompleteness::subject).toList());
    }

    /** A row that could be placed leaves nothing behind. */
    @Test
    void rowsThatWerePlacedSayNothing() {
        assertEquals(List.of(), of(row(Classification.in("Domestic"), null)));
    }
}
