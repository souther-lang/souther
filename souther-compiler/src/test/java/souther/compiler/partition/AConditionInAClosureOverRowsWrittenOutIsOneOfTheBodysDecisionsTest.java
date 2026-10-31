package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A comparison written in a closure applied to each of the rows a container was written with draws
 * a line for each row, and the body tells apart the classes those lines make by the ways it takes:
 * the arms of a fork on what the operation answers, and the two ways a comparison inside it comes
 * out.
 *
 * <p>The thresholds are 100 and 200 throughout, so the classes are below 100, from 100 to 200
 * and from 200.
 */
class AConditionInAClosureOverRowsWrittenOutIsOneOfTheBodysDecisionsTest {

    private static final String MODEL = """
            module kept
            data Row = { bound: Int }
            let table: List<Row> = [ Row { bound = 100 }, Row { bound = 200 } ]
            let swapped: List<Row> = [ Row { bound = 200 }, Row { bound = 100 } ]
            let none: List<Row> = []

            behavior byAny : (pay: Int) -> Ok | No
            let byAny (pay) = {
                guard List.any(r -> r.bound <= pay, table) else No
                Ok
            }

            behavior byAnyInTheOtherOrder : (pay: Int) -> Ok | No
            let byAnyInTheOtherOrder (pay) = {
                guard List.any(r -> r.bound <= pay, swapped) else No
                Ok
            }

            behavior byAll : (pay: Int) -> Ok | No
            let byAll (pay) = {
                guard List.all(r -> r.bound <= pay, table) else No
                Ok
            }

            behavior byCount : (pay: Int) -> Int
            let byCount (pay) = List.length(List.filter(r -> r.bound <= pay, table))

            behavior byNoRows : (pay: Int) -> Ok | No
            let byNoRows (pay) = {
                guard List.any(r -> r.bound <= pay, none) else No
                Ok
            }

            data Paid = { amount: Int }
                invariant amount >= 0
            let includingTheFloor: List<Row> =
                [ Row { bound = 0 }, Row { bound = 100 }, Row { bound = 200 } ]

            behavior anyBesideARowEveryValueMeets : (paid: Paid) -> Ok | No
            let anyBesideARowEveryValueMeets (paid) = {
                guard List.any(r -> r.bound <= paid.amount, [ Row { bound = 100 }, Row { bound = 0 } ])
                        else No
                Ok
            }

            behavior countBesideARowEveryValueMeets : (paid: Paid) -> Int
            let countBesideARowEveryValueMeets (paid) =
                List.length(List.filter(r -> r.bound <= paid.amount, includingTheFloor))

            behavior byFold : (paid: Paid) -> Int
            let byFold (paid) =
                List.fold((acc, r) -> if r.bound <= paid.amount then acc + 1 else acc, 0, table)

            data Flags = { each: List<Bool> }

            behavior besideAnotherCopyOfTheComparison : (paid: Paid) -> Flags | No
                constructs Flags
            let besideAnotherCopyOfTheComparison (paid) = {
                guard List.any(r -> r.bound <= paid.amount, table) else No
                Flags { each = List.map(r -> r.bound <= paid.amount, table) }
            }

            behavior byAFlagToo : (pay: Int, flag: Bool) -> Ok | No
            let byAFlagToo (pay, flag) = {
                guard List.any(r -> r.bound <= pay && flag, table) else No
                Ok
            }
            """;

    private static final List<String> BELOW = List.of("pay: x < 100");
    private static final List<String> BETWEEN = List.of("pay: 100 <= x < 200");
    private static final List<String> FROM_BOTH = List.of("pay: 100 <= x");
    private static final List<String> ABOVE = List.of("pay: 200 <= x");

    @Test
    void someRowMeetingTellsApartWhereTheFirstLineIs() {
        assertEquals(new BodyDistinction.Drawn(List.of(BELOW, FROM_BOTH)),
                toldApart("byAny").get("pay"));
    }

    /**
     * The arms are what the body takes, whichever row the operation meets first: the same two
     * groups, over the three classes both lines make once the row meeting 200 comes first.
     */
    @Test
    void theOrderOfTheRowsIsNotWhatTheArmsTellApartBy() {
        assertEquals(new BodyDistinction.Drawn(List.of(BELOW, List.of(BETWEEN.getFirst(),
                        ABOVE.getFirst()))),
                toldApart("byAnyInTheOtherOrder").get("pay"));
    }

    @Test
    void everyRowMeetingTellsApartWhereTheLastLineIs() {
        assertEquals(new BodyDistinction.Drawn(List.of(
                        List.of(BELOW.getFirst(), BETWEEN.getFirst()), ABOVE)),
                toldApart("byAll").get("pay"));
    }

    /** Both ways the comparison comes out are taken by the class between the lines. */
    @Test
    void aCountOfTheRowsMeetingTellsApartByEachLine() {
        assertEquals(new BodyDistinction.Drawn(List.of(BELOW, BETWEEN, ABOVE)),
                toldApart("byCount").get("pay"));
    }

    @Test
    void noRowsAreNoApplicationOfTheClosure() {
        assertEquals(Map.of(), toldApart("byNoRows"));
    }

    /**
     * A row the comparison comes out the same on for every value draws no line, and is still a row:
     * the statement it makes is not the one the others make, so what the lines drawn say of the
     * rest is not what the body tells apart by.
     */
    @Test
    void aRowEveryValueMeetsIsNotLeftOutOfWhatSomeRowMeetingTellsApartBy() {
        assertInstanceOf(BodyDistinction.Unread.class,
                toldApart("anyBesideARowEveryValueMeets").get("paid.amount"));
    }

    @Test
    void aRowEveryValueMeetsIsNotLeftOutOfWhatACountOfTheRowsMeetingTellsApartBy() {
        assertInstanceOf(BodyDistinction.Unread.class,
                toldApart("countBesideARowEveryValueMeets").get("paid.amount"));
    }

    /**
     * What a fork's statement accounts for is the comparisons written in its condition. Another
     * comparison drawing the same lines for the same relation is another rule, and what the
     * statement says is no reading of it.
     */
    @Test
    void aCopyOfTheComparisonElsewhereIsNotReadByTheStatementOfAnother() {
        assertEquals(new BodyDistinction.Unread(List.of(
                                List.of("paid.amount: 0 <= x < 100"),
                                List.of("paid.amount: 100 <= x < 200", "paid.amount: 200 <= x")),
                        true),
                toldApart("besideAnotherCopyOfTheComparison").get("paid.amount"));
    }

    /** The step of a fold that keeps one side is a fork on the comparison, decided on each row. */
    @Test
    void aFoldKeepingOneSideTellsApartByEachLine() {
        assertEquals(new BodyDistinction.Drawn(List.of(List.of("paid.amount: 0 <= x < 100"),
                        List.of("paid.amount: 100 <= x < 200"), List.of("paid.amount: 200 <= x"))),
                toldApart("byFold").get("paid.amount"));
    }

    /** What the lines do not settle is left unread, as it was. */
    @Test
    void aStatementBesideAFlagIsNotSettledByTheLinesOfTheRows() {
        assertInstanceOf(BodyDistinction.Unread.class, toldApart("byAFlagToo").get("pay"));
    }

    private static final Map<String, PartitionEvidence> MEASURED = measured();

    private static Map<String, BodyDistinction> toldApart(String behavior) {
        Map<String, BodyDistinction> out = new LinkedHashMap<>();
        MEASURED.get(behavior).axes().forEach(axis -> out.put(axis.name(), axis.toldApart()));
        return out;
    }

    private static Map<String, PartitionEvidence> measured() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(each -> each.diagnostic().code()).toList(),
                "the model under test compiles");
        return compilation.db().ask(new Adequacy.Coverage("kept")).value();
    }
}
