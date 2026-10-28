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
