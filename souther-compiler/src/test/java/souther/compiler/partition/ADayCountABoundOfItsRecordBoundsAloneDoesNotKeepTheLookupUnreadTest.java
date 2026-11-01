package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.AdequacyReport;

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
            data Window = { first: Pay, second: Pay, third: Pay }
            data Row = { grade: Int, lowerBound: Yen }
            data Decision = { grade: Int }
            let table: List<Row> = [
                Row { grade = 1, lowerBound = Yen(0) },
                Row { grade = 2, lowerBound = Yen(1000) },
                Row { grade = 3, lowerBound = Yen(2000) } ]
            let totalOf (p: Pay): Yen = p.a
            let gradeRowFor (m: Yen): Row =
                List.fold((acc, r) -> if r.lowerBound <= m then r else acc,
                          Row { grade = 0, lowerBound = Yen(0) }, table)
            let monthsOf (w: Window): List<Pay> = [ w.first, w.second, w.third ]
            let averageOf (records: List<Pay>): Yen =
                Yen(Rational.toInt(DOWN,
                    List.sum(List.map(p -> totalOf(p).value, records)) / List.length(records)))

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
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList(),
                "the model under test compiles");
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

    @Test
    void daysBoundedByTheirRecordAloneAreReadAsDaysOfTheirOwnAre() {
        PartitionEvidence alone = withDaysAnInt(BOUNDED_ALONE);

        assertEquals(List.of(), alone.unanswered());
        assertEquals(withDaysANewtype().notRead(), alone.notRead());
    }

    @Test
    void daysHeldBesideThePayTheAverageIsOfAreNotGivenAValueApartFromIt() {
        assertFalse(withDaysAnInt(BESIDE_THE_PAY).unanswered().isEmpty());
    }

    @Test
    void rulesJoinedInOneClauseAreReadAsTheyAreOnSeparateLines() {
        String oneClause = PAY + """
                data Pay = { a: Yen, days: Int }
                    invariant a.value <= 1000000000000 && days >= 0 && days <= 31
                """ + REST;

        PartitionEvidence joined = partitionOf(oneClause);

        assertEquals(List.of(), joined.unanswered());
        assertEquals(withDaysAnInt(BOUNDED_ALONE).notRead(), joined.notRead());
    }

    @Test
    void daysHeldBesideThePayByARuleJoinedInOneClauseAreNotGivenAValueApartFromIt() {
        String oneClause = PAY + """
                data Pay = { a: Yen, days: Int }
                    invariant a.value <= 1000000000000 && days >= 0 && days <= a.value
                """ + REST;

        assertFalse(partitionOf(oneClause).unanswered().isEmpty());
    }
}
