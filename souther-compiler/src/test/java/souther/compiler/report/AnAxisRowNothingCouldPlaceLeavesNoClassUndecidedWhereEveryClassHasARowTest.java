package souther.compiler.report;

import souther.compiler.observe.Incompleteness;
import souther.compiler.query.Measurement;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.query.Weakening;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row that could not be placed at a position leaves undecided only a class no row is in, and
 * the combinations such a class takes part in.
 *
 * <p>The sum {@code Flag} has two classes. The first row below is so large that the observation is
 * cut short before it reaches the flag, so it cannot be placed there; the rows after it are small
 * and are in one class each. Whether the first row would have been in {@code Yes} or {@code No}
 * changes nothing the measure says: both have a row.
 */
class AnAxisRowNothingCouldPlaceLeavesNoClassUndecidedWhereEveryClassHasARowTest {

    private static String model(String smallRows) {
        return """
                module example.budget

                data Amount = Int
                    invariant value >= 0 && value <= 1000

                data Yes
                data No
                data Flag = Yes | No

                data Item = { a: String, b: String, c: String }
                data Group = { items: List<Item> }

                data Draft = { groups: List<Group>, cost: Amount, flag: Flag }
                data Ok = { n: Int }

                behavior take : (request: Draft) -> Ok
                    constructs Ok

                let take (request) =
                    match request.flag with | Yes | No -> Ok { n = request.cost.value }

                let someItems (n: Int): List<Item> =
                    List.map({ (i) -> Item { a = "x", b = "x", c = "x" } }, List.rangeInclusive(1, n))

                let someGroups (n: Int): List<Group> =
                    List.map({ (i) -> Group { items = someItems(64) } }, List.rangeInclusive(1, n))

                example take
                    | (Draft { groups = someGroups(64), cost = Amount(0), flag = Yes }) -> Ok { n = 0 }
                """ + smallRows;
    }

    private static PartitionEvidence.AxisCoverage theFlag(AdequacyReport report) {
        return report.modules().getFirst().behaviors().getFirst().partition().axes().stream()
                .filter(each -> each.path().endsWith("flag"))
                .findFirst().orElseThrow();
    }

    /** Both classes have a row that was placed, so the row that was not decides nothing. */
    @Test
    void everyClassWithARowLeavesTheMeasureComplete() {
        AdequacyReport report = WrittenWitness.reportOf(model("""
                    | (Draft { groups = [], cost = Amount(0), flag = Yes }) -> Ok { n = 0 }
                    | (Draft { groups = [], cost = Amount(0), flag = No }) -> Ok { n = 0 }
                """));
        PartitionEvidence.AxisCoverage flag = theFlag(report);

        assertEquals(1, flag.reached().made().orElseThrow().unclassifiedRows(),
                "the first row is still not placed");
        assertInstanceOf(Measurement.Complete.class, flag.reached(),
                () -> "every class has a row, and it says " + flag.reached());
    }

    /**
     * Two flags, tried against each other. The first row is cut short before either, so it cannot
     * be placed at them; the rows after it are one apiece in a combination.
     */
    private static String twoFlags(String smallRows) {
        return """
                module example.budget

                data Yes
                data No
                data Flag = Yes | No

                data Item = { a: String, b: String, c: String }
                data Group = { items: List<Item> }

                data Draft = { groups: List<Group>, flag: Flag, other: Flag }
                data Ok = { n: Int }

                behavior take : (request: Draft) -> Ok
                    constructs Ok

                let take (request) =
                    match request.flag with
                        | Yes -> match request.other with | Yes -> Ok { n = 0 } | No -> Ok { n = 1 }
                        | No -> match request.other with | Yes -> Ok { n = 2 } | No -> Ok { n = 3 }

                let someItems (n: Int): List<Item> =
                    List.map({ (i) -> Item { a = "x", b = "x", c = "x" } }, List.rangeInclusive(1, n))

                let someGroups (n: Int): List<Group> =
                    List.map({ (i) -> Group { items = someItems(64) } }, List.rangeInclusive(1, n))

                example take
                    | (Draft { groups = someGroups(64), flag = Yes, other = Yes }) -> Ok { n = 0 }
                """ + smallRows;
    }

    private static final String YES_YES =
            "    | (Draft { groups = [], flag = Yes, other = Yes }) -> Ok { n = 0 }\n";
    private static final String YES_NO =
            "    | (Draft { groups = [], flag = Yes, other = No }) -> Ok { n = 1 }\n";
    private static final String NO_YES =
            "    | (Draft { groups = [], flag = No, other = Yes }) -> Ok { n = 2 }\n";
    private static final String NO_NO =
            "    | (Draft { groups = [], flag = No, other = No }) -> Ok { n = 3 }\n";

    /** Every combination has a row that was placed, so the row that was not decides nothing. */
    @Test
    void everyCombinationWithARowLeavesThePairsComplete() {
        AdequacyReport report = WrittenWitness.reportOf(
                twoFlags(YES_YES + YES_NO + NO_YES + NO_NO));
        PartitionEvidence.PairSpace pairs =
                report.modules().getFirst().behaviors().getFirst().partition().pairs();

        assertEquals(1, pairs.space().size(), "the two flags are one relation");
        assertInstanceOf(Measurement.Complete.class, pairs.counted(),
                () -> "every combination has a row, and it says " + pairs.counted());
    }

    /** With no row in {@code No, No}, the row nothing could place may be the one in it. */
    @Test
    void aCombinationNoRowIsInIsUndecidedWhereARowCouldNotBePlaced() {
        AdequacyReport report = WrittenWitness.reportOf(twoFlags(YES_YES + YES_NO + NO_YES));
        PartitionEvidence.PairSpace pairs =
                report.modules().getFirst().behaviors().getFirst().partition().pairs();

        assertInstanceOf(Measurement.Partial.class, pairs.counted(),
                () -> "No, No may be where the first row is: " + pairs.counted());
    }

    /** With no row in {@code No}, the row nothing could place may be the one in it. */
    @Test
    void aClassNoRowIsInIsUndecidedWhereARowCouldNotBePlaced() {
        AdequacyReport report = WrittenWitness.reportOf(model("""
                    | (Draft { groups = [], cost = Amount(0), flag = Yes }) -> Ok { n = 0 }
                """));
        PartitionEvidence.AxisCoverage flag = theFlag(report);

        Measurement.Partial<?> partial = assertInstanceOf(Measurement.Partial.class,
                flag.reached(), () -> "No may be where the first row is: " + flag.reached());
        assertTrue(partial.weakening().causes().stream().anyMatch(each ->
                        each instanceof Weakening.ObservationIncomplete it
                                && it.met().fact().code() == Incompleteness.Code.VALUE_TRUNCATED),
                () -> partial.weakening().causes().toString());
    }
}
