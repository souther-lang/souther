package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.check.RuleRef;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.AdequacyReport;
import souther.compiler.types.WrittenOwner;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A lookup of an average, after an {@code if} that tests the lookup's own value, with the months'
 * days asked apart, is read where the days are bounded by invariants of the record they are in.
 *
 * <p>Those invariants name {@code days}, though they bound it alone, so the days are given a value
 * apart from the average, as they are where {@code days} is a newtype bounding its own value:
 * the months that are kept are decided by them, and some value of them meets what the way past
 * the {@code if} asks. Where an invariant holds {@code days} beside the pay the average is of,
 * they are not, and the lookup is left unanswered.
 */
class ADayCountABoundOfItsRecordBoundsAloneDoesNotKeepTheLookupUnreadTest {

    private static final String PAY = """
            module demo

            data Yen = Int
                invariant value >= 0
            """;

    private static final String PAY_RECORD = """
            data Pay = { a: Yen, days: %s }
                invariant a.value <= 1000000000000
            """;

    private static final String BOUNDED_ALONE = "    invariant days >= 0\n"
            + "    invariant days <= 31\n";

    private static final String BESIDE_THE_PAY = "    invariant days >= 0\n"
            + "    invariant days <= a.value\n";

    private static final String DAYS_OF_THEIR_OWN = """
            data Days = Int
                invariant value >= 0 && value <= 31
            """;

    private static final String REST = """
            data Window = { first: Pay, second: Pay }
            data Row = { grade: Int, lowerBound: Yen }
            data Decision = { grade: Int }
            let table: List<Row> = [
                Row { grade = 1, lowerBound = Yen(0) },
                Row { grade = 2, lowerBound = Yen(1000) } ]
            let gradeRowFor (m: Yen): Row =
                List.fold((acc, r) -> if r.lowerBound <= m then r else acc,
                          Row { grade = 0, lowerBound = Yen(0) }, table)
            let monthsOf (w: Window): List<Pay> = [ w.first, w.second ]
            let averageOf (records: List<Pay>): Yen =
                Yen(Rational.toInt(DOWN,
                    List.sum(List.map(p -> p.a.value, records)) / List.length(records)))

            data NotRequired = { reasons: List<Int> }
                invariant List.length(reasons) >= 1
            let blockers (current: Decision, w: Window, computed: Int): List<Int> =
                   List.map(r -> 3, List.filter(r -> r.days < 17, monthsOf(w)))
                ++ [ 2 | Int.abs(computed - current.grade) < 2 ]

            behavior f : (current: Decision, w: Window) -> Decision | NotRequired
                constructs Decision, Row, Yen, NotRequired
            let f (current, w) = {
                let average = averageOf(monthsOf(w))
                let computed = gradeRowFor(average).grade
                if NotRequired { reasons = blockers(current, w, computed) } as unchanged
                then unchanged
                else Decision { grade = gradeRowFor(average).grade }
            }
            """;

    private static PartitionEvidence partitionOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        ACompiledModel.compiles(compilation);
        List<AdequacyReport.BehaviorReport> behaviors =
                AdequacyReport.of(compilation).modules().get(0).behaviors();
        assertEquals(1, behaviors.size());
        return behaviors.get(0).partition();
    }

    private static PartitionEvidence withDaysAnInt(String rules) {
        return partitionOf(PAY + PAY_RECORD.formatted("Int") + rules + REST);
    }

    private static PartitionEvidence withDaysANewtype() {
        return partitionOf(PAY + DAYS_OF_THEIR_OWN + PAY_RECORD.formatted("Days") + REST);
    }

    /**
     * What {@code measured} leaves unanswered apart from the blockers' comparison. A grade of any
     * whole number less the one the table gives may pass an {@code Int}, so that comparison is not
     * shown past for every value whatever the days are; what turns on the days is the lookup.
     */
    private static List<PartitionEvidence.Unanswered> unansweredBesideTheGrade(
            PartitionEvidence measured) {
        return measured.unanswered().stream()
                .filter(each -> !(each.rule() instanceof RuleRef.Written written
                        && written.origin().owner() instanceof WrittenOwner.Body body
                        && body.definition().equals("blockers")))
                .toList();
    }

    /** Days the record's invariants bound alone leave nothing of the lookup unanswered, and leave
     *  unread what days of a newtype of their own leave. */
    @Test
    void daysBoundedByTheirRecordAloneAreReadAsDaysOfTheirOwnAre() {
        PartitionEvidence alone = withDaysAnInt(BOUNDED_ALONE);

        assertEquals(List.of(), unansweredBesideTheGrade(alone));
        assertEquals(withDaysANewtype().notRead(), alone.notRead());
    }

    /** Days an invariant holds beside the pay leave the lookup unanswered, and not only the
     *  blockers' comparison. */
    @Test
    void daysHeldBesideThePayTheAverageIsOfAreNotGivenAValueApartFromIt() {
        assertFalse(unansweredBesideTheGrade(withDaysAnInt(BESIDE_THE_PAY)).isEmpty());
    }
}
