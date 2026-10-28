package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which data a bound is read out of does not turn on how the data was reached: held in a field of a
 * record, read through a field of a field, or under a name of its own. Two tables are two lines and
 * one table is one, whichever way each is handed to the helper.
 */
class TheDataABoundIsReadOutOfIsTheSameHoweverItIsReachedTest {

    /** How a row holds its bound: in a field of its own, or in a field of a field. */
    private enum Shape {

        FLAT("data Row = { grade: Int, lowerBound: Int }",
                "Row { grade = 1, lowerBound = 0 }, Row { grade = 2, lowerBound = 100 }",
                "r.lowerBound"),

        NESTED("data Limit = { lowerBound: Int }\n"
                + "                data Row = { grade: Int, limit: Limit }",
                "Row { grade = 1, limit = Limit { lowerBound = 0 } },"
                        + " Row { grade = 2, limit = Limit { lowerBound = 100 } }",
                "r.limit.lowerBound");

        private final String declaration;
        private final String rows;
        private final String bound;

        Shape(String declaration, String rows, String bound) {
            this.declaration = declaration;
            this.rows = rows;
            this.bound = bound;
        }
    }

    private static String model(Shape shape, String call) {
        return """
                module demo

                data N = { v: Int }
                    invariant v >= 0
                %1$s
                data Config = { first: List<Row>, second: List<Row> }
                let first: List<Row> = [ %2$s ]
                let second: List<Row> = [ %2$s ]
                let config: Config = Config { first = [ %2$s ], second = [ %2$s ] }
                let gradeIn (rows: List<Row>, m: Int): Int =
                    List.fold((acc, r) -> if %3$s <= m then r.grade else acc, 0, rows)

                behavior f : (a: N, useFirst: Bool) -> Int

                let f (a, useFirst) =
                    %4$s

                example f
                    | (N { v = 100 }, true) -> 2
                    | (N { v = 99 }, true) -> 1
                    | (N { v = 101 }, true) -> 2
                    | (N { v = 98 }, true) -> 1
                """.formatted(shape.declaration, shape.rows, shape.bound, call);
    }

    private static final String TWO_TABLES =
            "if useFirst then gradeIn(first, a.v) else gradeIn(second, a.v)";

    private static List<String> owedAtTheBound(String report) {
        return report.lines().filter(each -> each.contains("no row is at the"))
                .filter(each -> each.contains("(comparison@"))
                .filter(each -> each.contains("ON point") || each.contains("OFF point"))
                .toList();
    }

    /** A bound read through a field of a field is read out of the table it is a field of. */
    @Test
    void aNestedFieldIsReadOutOfTheTableItIsAFieldOf() {
        assertOwedAtTheBound(2, Shape.NESTED, TWO_TABLES);
    }

    /** A table held in a field of a record, given from two calls, is one table. */
    @Test
    void aTableInAFieldGivenFromTwoCallsIsOne() {
        assertOwedAtTheBound(0, Shape.FLAT, "if useFirst then gradeIn(config.first, a.v)"
                + " else gradeIn(config.first, a.v)");
    }

    /** Two tables held in two fields of one record are two. */
    @Test
    void twoFieldsOfOneRecordAreTwoTables() {
        assertOwedAtTheBound(2, Shape.FLAT, "if useFirst then gradeIn(config.first, a.v)"
                + " else gradeIn(config.second, a.v)");
    }

    private static String limits(String second, String chosen) {
        return """
                module demo

                data N = { v: Int }
                    invariant v >= 0
                data Limit = { lowerBound: Int }
                let first: Limit = Limit { lowerBound = 100 }
                let second: Limit = Limit { lowerBound = %s }

                behavior f : (a: N, useFirst: Bool) -> Int

                let f (a, useFirst) =
                    { let chosen = %s
                        if chosen.lowerBound <= a.v then 2 else 1 }

                example f
                    | (N { v = 100 }, true) -> 2
                    | (N { v = 99 }, true) -> 1
                    | (N { v = 101 }, true) -> 2
                    | (N { v = 98 }, true) -> 1
                """.formatted(second, chosen);
    }

    /** A limit a condition chooses is whichever the condition says: rows through the first leave
     *  the points where the second is chosen owed. */
    @Test
    void aLimitChosenByAConditionIsOwedWhereEachIsChosen() {
        String report = reportOf(limits("100", "if useFirst then first else second"));
        assertTrue(owedAtTheBound(report).stream()
                .anyMatch(each -> each.contains("ON point")), report);
        assertTrue(report.contains("where useFirst is false"), report);
    }

    /** And a bound written wrong in the one rows never choose is shown by no row. */
    @Test
    void aBoundWrittenWrongInTheLimitNoRowChoosesIsOwed() {
        String report = reportOf(limits("1000", "if useFirst then first else second"));
        assertTrue(report.contains("= 1000"), report);
    }

    /** A limit handed to a helper is chosen the same way. */
    @Test
    void aLimitHandedToAHelperAfterAChoiceIsOwedWhereEachIsChosen() {
        String report = reportOf(limits("1000", "if useFirst then first else second")
                .replace("if chosen.lowerBound <= a.v then 2 else 1",
                        "atLeast(chosen, a.v)")
                .replace("behavior f :", "let atLeast (l: Limit, m: Int): Int =\n"
                        + "                    if l.lowerBound <= m then 2 else 1\n\n"
                        + "                behavior f :"));
        assertTrue(report.contains("= 1000"), report);
    }

    /** A table a condition chooses is no position a fold runs over, which the report says in so
     *  many words and never as every point met. */
    @Test
    void aTableChosenByAConditionIsSaidToBeUnreadNotMet() {
        String report = reportOf(model(Shape.FLAT,
                "{ let chosen = if useFirst then first else second\n        gradeIn(chosen, a.v) }"));
        assertTrue(report.contains("what is no position of the input"), report);
        assertTrue(report.contains("adequacy: not satisfied"), report);
    }

    private static void assertOwedAtTheBound(int expected, Shape shape, String call) {
        String report = reportOf(model(shape, call));
        assertEquals(expected, owedAtTheBound(report).size(), report);
    }

    private static String reportOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String report = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
        assertTrue(report.contains("1 behavior:"), "the model was measured: " + report);
        return report;
    }
}
