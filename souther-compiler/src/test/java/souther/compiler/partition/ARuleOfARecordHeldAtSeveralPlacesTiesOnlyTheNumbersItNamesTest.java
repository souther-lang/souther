package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A rule of a record held at several places of an input ties the numbers it names at one place,
 * and nothing at another. {@code base + sched <= M} of a month ties that month's two amounts to
 * one another, and the amounts of another month to nothing here.
 */
class ARuleOfARecordHeldAtSeveralPlacesTiesOnlyTheNumbersItNamesTest {

    private static final String SOURCE = """
            module demo

            data Yen = Int
                invariant value >= 0 && value <= 1000000000000
            data Rem = { base: Yen, sched: Yen }
                invariant base.value + sched.value <= 1000000000000
            data Month = { rem: Rem }
            data Window = { first: Month, second: Month, third: Month }
            data Row = { grade: Int, lowerBound: Int }
            data Decision = { grade: Int }
            let table: List<Row> = [
                Row { grade = 1, lowerBound = -100 },
                Row { grade = 2, lowerBound = 0 },
                Row { grade = 3, lowerBound = 100 } ]
            let gradeRowFor (m: Int): Row =
                List.fold((acc, r) -> if r.lowerBound <= m then r else acc,
                          Row { grade = 0, lowerBound = -200 }, table)

            behavior f : (w: Window) -> Decision
                constructs Decision, Row
            let f (w) = Decision { grade = gradeRowFor(%s).grade }
            """;

    /** The same, behind a guard on an amount of the second month. */
    private static final String GUARDED = SOURCE.replace("""
            behavior f : (w: Window) -> Decision
                constructs Decision, Row
            let f (w) = Decision { grade = gradeRowFor(%s).grade }
            """, """
            data Skipped
            behavior f : (w: Window) -> Decision | Skipped
                constructs Decision, Row
            let f (w) = {
                guard w.second.rem.base.value > 5 else Skipped
                Decision { grade = gradeRowFor(%s).grade }
            }
            """);

    /** The places the report says nothing is read of. */
    private static List<String> unread(String looked) {
        return unreadIn(SOURCE, looked);
    }

    private static List<String> unreadIn(String source, String looked) {
        Compilation compilation = Compilation.ofSource(source.formatted(looked), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model under test compiles");
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts())).lines()
                .filter(line -> line.contains("not read:"))
                .map(line -> line.replaceAll(".*about `([^`]*)`.*", "$1"))
                .toList();
    }

    /** The amounts looked up are the two the rule of the first month names, and the rule of the
     *  other months names none of them. */
    @Test
    void theTotalOfOneMonthIsReadWhereTheRuleHoldsAtTheOthersToo() {
        assertEquals(List.of(), unread("w.first.rem.base.value + w.first.rem.sched.value"));
    }

    /** Two amounts of different months are tied by no rule, though each is tied to an amount
     *  that is not in the comparison. */
    @Test
    void amountsOfTwoMonthsAreTiedToNothingInTheComparison() {
        assertEquals(List.of(),
                unread("w.first.rem.base.value + w.second.rem.base.value"));
    }

    private static final String SIX_AMOUNTS = "w.first.rem.base.value + w.first.rem.sched.value"
            + " + w.second.rem.base.value + w.second.rem.sched.value"
            + " + w.third.rem.base.value + w.third.rem.sched.value";

    /** The comparison adds up three months, each a sum the rule of its month bounds, far above
     *  the lines: a row near a line has each month's total below the bound. */
    @Test
    void theTotalsOfSeveralMonthsAreReadWhereTheRulesBoundEachFarAboveTheLines() {
        assertEquals(List.of(), unread(SIX_AMOUNTS));
    }

    /** The same, rounded after a division, which is how an average is asked. */
    @Test
    void anAverageOfSeveralMonthsIsReadTheSameWay() {
        assertEquals(List.of(), unread("Rational.toInt(DOWN, (" + SIX_AMOUNTS + ") / 3)"));
    }

    /** Control: where the rule bounds a month at a figure a row near a line can reach, the rule
     *  is not held aside and the totals are not read. */
    @Test
    void aRuleABoundNearTheLinesCanReachIsKept() {
        String tight = SOURCE.replace("invariant base.value + sched.value <= 1000000000000",
                "invariant base.value + sched.value <= 50");
        assertFalse(unreadIn(tight, SIX_AMOUNTS).isEmpty());
    }

    /** Control: a guard on an amount of another month, whose rule is held aside with the first
     *  month's, speaks of a place that rule is about, so the rule is not held aside. */
    @Test
    void aGuardOnAnotherMonthKeepsTheRuleOfTheMonthLookedUp() {
        assertFalse(unreadIn(GUARDED,
                "w.first.rem.base.value + w.first.rem.sched.value").isEmpty());
    }

    /** Control: the two amounts of one month are tied by its rule, and a difference of them is
     *  no relation a rule that bounds their sum leaves room around. */
    @Test
    void aDifferenceOfTwoAmountsTheRuleTiesIsLeftUnread() {
        assertFalse(unread("w.first.rem.base.value - w.first.rem.sched.value").isEmpty());
    }
}
