package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A lookup of the last row of a table whose lower bound a total reaches reads the lower bound off
 * the row, and working out the row's other fields happens all the same. Those fields end no run
 * when they are written out: a construction of a number the clauses of its type leave stands where
 * the number written lies in what they leave, and a name handed to the helper that writes the row
 * is the number it was handed.
 */
class ARowOfATableWhoseOtherFieldsAreWrittenOutLeavesItsLookupReadTest {

    private static final String SOURCE = """
            module demo

            data Yen = Int
                invariant value >= 0
            data Grade = Int
                invariant value >= 1
            data Rem = { base: Yen, sched: Yen, commute: Yen, excl: Yen, variable: Yen }
            data Row = { grade: Grade, rank: Int, std: Yen, lowerBound: Yen }
            data Decision = { grade: Int }
            %s
            let totalOf (r: Rem): Yen = r.base + r.sched + r.commute + r.excl + r.variable
            let gradeRowFor (m: Yen): Row =
                List.fold((acc, r) -> if r.lowerBound <= m then r else acc,
                          Row { grade = Grade(1), rank = 0, std = Yen(0), lowerBound = Yen(0) },
                          table)
            let decisionFor (m: Yen): Decision = {
                let row = gradeRowFor(m)
                Decision { grade = row.grade.value }
            }

            behavior f : (r: Rem) -> Decision
                constructs Decision, Row, Yen, Grade
            let f (r) = decisionFor(totalOf(r))
            """;

    /** The places the report says nothing is read of. */
    private static List<String> unread(String table) {
        Compilation compilation = Compilation.ofSource(SOURCE.formatted(table), "Main");
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

    private static final String STOPPING_BEFORE_THE_NUMBER = """
            module demo

            data Yen = Int
                invariant value >= 0
            data Rem = { base: Yen, sched: Yen, commute: Yen, excl: Yen, variable: Yen }
            data Row = { std: Yen, lowerBound: Yen }
            data Decision = { std: Int }
            %s
            let totalOf (r: Rem): Yen = r.base + r.sched + r.commute + r.excl + r.variable
            let gradeRowFor (m: Yen, k: Int): Row =
                List.fold((acc, r) -> if r.lowerBound <= m then r else acc,
                          Row { std = Yen(0), lowerBound = Yen(0) },
                          [ %s, %s ])

            behavior f : (r: Rem, k: Int) -> Decision
                constructs Decision, Row, Yen
            let f (r, k) = {
                let row = gradeRowFor(totalOf(r), k)
                Decision { std = row.std.value }
            }
            """;

    private static List<String> unreadStoppingBeforeTheNumber(String helpers, String first,
                                                                String second) {
        Compilation compilation = Compilation.ofSource(
                STOPPING_BEFORE_THE_NUMBER.formatted(helpers, first, second), "Main");
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

    private static final List<String> EVERY_PLACE_OF_THE_TOTAL =
            List.of("r.base", "r.commute", "r.excl", "r.sched", "r.variable");

    /** The control: what the helper works out before it answers five ends no run. */
    @Test
    void aWorkingOutBeforeTheNumberThatEndsNoRunIsFollowed() {
        assertEquals(List.of(), unreadStoppingBeforeTheNumber("""
                let five (n: Int): Yen = {
                    let unused = 7
                    Yen(5)
                }
                """, "Row { std = five(0), lowerBound = Yen(0) }",
                "Row { std = five(0), lowerBound = Yen(100) }"));
    }

    /** What the helper works out before it answers five is worked out all the same: the number
     *  it answers is five whatever that is, and a run can stop before it is answered. */
    @Test
    void anOperationBeforeTheNumberIsStillWorkedOut() {
        assertEquals(EVERY_PLACE_OF_THE_TOTAL, unreadStoppingBeforeTheNumber("""
                let five (n: Int): Yen = {
                    let unused = n + 1
                    Yen(5)
                }
                """, "Row { std = five(0), lowerBound = Yen(0) }",
                "Row { std = five(0), lowerBound = Yen(100) }"));
    }

    /** The same before the row itself is made: the row is what the helper answers last. */
    @Test
    void anOperationBeforeTheRowIsStillWorkedOut() {
        assertEquals(EVERY_PLACE_OF_THE_TOTAL, unreadStoppingBeforeTheNumber("""
                let rowAt (n: Int, lowerBound: Int): Row = {
                    let unused = n + 1
                    Row { std = Yen(5), lowerBound = Yen(lowerBound) }
                }
                """, "rowAt(0, 0)", "rowAt(0, 100)"));
    }

    /** The control for the row: what the helper works out before it answers ends no run. */
    @Test
    void aWorkingOutBeforeTheRowThatEndsNoRunIsFollowed() {
        assertEquals(List.of(), unreadStoppingBeforeTheNumber("""
                let rowAt (n: Int, lowerBound: Int): Row = {
                    let unused = 7
                    Row { std = Yen(5), lowerBound = Yen(lowerBound) }
                }
                """, "rowAt(0, 0)", "rowAt(0, 100)"));
    }

    @Test
    void constructionsOfNumbersTheirTypesLeaveEndNoRun() {
        assertEquals(List.of(), unread("""
                let table: List<Row> = [
                    Row { grade = Grade(1), rank = 1, std = Yen(5), lowerBound = Yen(0) },
                    Row { grade = Grade(2), rank = 2, std = Yen(6), lowerBound = Yen(100) },
                    Row { grade = Grade(3), rank = 3, std = Yen(7), lowerBound = Yen(200) } ]
                """));
    }

    @Test
    void aRowHandedToAHelperThatWritesItEndsNoRun() {
        assertEquals(List.of(), unread("""
                let row (g: Int, std: Int, lb: Int): Row =
                    Row { grade = Grade(g), rank = g, std = Yen(std), lowerBound = Yen(lb) }
                let table: List<Row> = [ row(1, 5, 0), row(2, 6, 100), row(3, 7, 200) ]
                """));
    }
}
