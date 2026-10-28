package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

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

    /** A helper over a limit, applied to two limits whose bounds are alike. */
    private static String helperOver(String body, String call) {
        return """
                module demo

                data N = { v: Int }
                    invariant v >= 0
                data Limit = { lowerBound: Int }
                let first: Limit = Limit { lowerBound = 100 }
                let second: Limit = Limit { lowerBound = 100 }
                let atLeast (l: Limit, m: Int): Int =
                    %s

                behavior f : (a: N, useFirst: Bool) -> Int

                let f (a, useFirst) =
                    %s

                example f
                    | (N { v = 100 }, true) -> 2
                    | (N { v = 99 }, true) -> 1
                    | (N { v = 101 }, true) -> 2
                    | (N { v = 98 }, true) -> 1
                """.formatted(body, call);
    }

    private static final String TWO_LIMITS =
            "if useFirst then atLeast(first, a.v) else atLeast(second, a.v)";

    private static final String WRITTEN = "if l.lowerBound <= m then 2 else 1";

    /** A bound given a name of its own is read out of what it was a field of: the same as the
     *  bound written where it is compared. */
    @Test
    void aBoundNamedByALetIsReadOutOfTheDataItIsAFieldOf() {
        String named = "{ let bound = l.lowerBound\n        if bound <= m then 2 else 1 }";
        assertEquals(placesInTheDocument(helperOver(WRITTEN, TWO_LIMITS)),
                placesInTheDocument(helperOver(named, TWO_LIMITS)));
        assertEquals(2, placesInTheDocument(helperOver(named, TWO_LIMITS)).size());
        // The same points are owed, wherever in the source each form puts the comparison.
        assertEquals(owedAtTheBound(reportOf(helperOver(WRITTEN, TWO_LIMITS))).size(),
                owedAtTheBound(reportOf(helperOver(named, TWO_LIMITS))).size());
    }

    /** A bound arithmetic over a named field is read out of the same data. */
    @Test
    void aBoundMadeOfANamedFieldIsReadOutOfTheDataItIsAFieldOf() {
        String named = "{ let bound = l.lowerBound\n        if bound + 1 <= m then 2 else 1 }";
        assertEquals(2, placesInTheDocument(helperOver(named, TWO_LIMITS)).size());
    }

    /** A number handed to a helper is read out of what the caller read it out of: a field of a
     *  limit handed as a number is that limit's, and two calls with two limits are two data. */
    @Test
    void aNumberHandedFromAFieldIsReadOutOfTheDataItIsAFieldOf() {
        String source = helperOver("if b <= m then 2 else 1",
                "if useFirst then atLeast(first.lowerBound, a.v)"
                        + " else atLeast(second.lowerBound, a.v)")
                .replace("(l: Limit, m: Int)", "(b: Int, m: Int)");
        assertEquals(2, placesInTheDocument(source).size());
    }

    /** And a literal handed to it is no data, so two calls with two literals are one line. */
    @Test
    void aNumberHandedAsALiteralIsNoData() {
        String source = helperOver("if b <= m then 2 else 1",
                "if useFirst then atLeast(100, a.v) else atLeast(200, a.v)")
                .replace("(l: Limit, m: Int)", "(b: Int, m: Int)");
        assertEquals(Set.of(), placesInTheDocument(source));
    }

    /** The same limit under two names, its bound named by a `let`, is one line: nothing is owed
     *  of the second name that the first did not owe. */
    @Test
    void aNamedBoundOfOneLimitUnderTwoNamesIsOne() {
        String call = "{ let alias = first\n        if useFirst then atLeast(first, a.v)"
                + " else atLeast(alias, a.v) }";
        String named = "{ let bound = l.lowerBound\n        if bound <= m then 2 else 1 }";
        assertEquals(List.of(), owedAtTheBound(reportOf(helperOver(named, call))));
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
        assertTrue(isOwedAt(report, "ON point", "= 1000"), report);
        assertTrue(isOwedAt(report, "OFF point", "= 999"), report);
    }

    /** Whether a point of the given kind is owed a row, and says it is read as {@code reading}:
     *  a gap the report marks, and not a number it happens to print. */
    private static boolean isOwedAt(String report, String point, String reading) {
        List<String> lines = report.lines().toList();
        for (int i = 0; i + 1 < lines.size(); i++) {
            if (lines.get(i).contains("! no row is at the " + point)
                    && lines.get(i + 1).contains(reading)) {
                return true;
            }
        }
        return false;
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
        // The region the wrong bound opens is a gap no row of the first limit closes, and the
        // point at it is answered at one reading of the line and not at the one where the second
        // limit is chosen.
        assertTrue(report.contains("! no row is in `a.v/1000 <= x` at a.v"), report);
        assertTrue(report.contains("is answered, and not at every reading of the line"), report);
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

    /** Every place the document says a bound is read out of, each once. */
    private static Set<String> placesInTheDocument(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String json = AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts()));
        Set<String> out = new TreeSet<>();
        String quoted = "\"(?:[^\"\\\\]|\\\\.)*\"";
        Matcher lists = Pattern.compile("\"heldIn\"\\s*:\\s*\\[((?:\\s*" + quoted + "\\s*,?)*)\\s*]")
                .matcher(json);
        while (lists.find()) {
            Matcher each = Pattern.compile("\"((?:[^\"\\\\]|\\\\.)*)\"").matcher(lists.group(1));
            while (each.find()) {
                out.add(each.group(1));
            }
        }
        return out;
    }

    /** What the document says a bound is read out of is the location and nothing a reader calls
     *  it, so one table reached under two names is one entry however many times it is met. */
    @Test
    void theDocumentSaysWhereABoundIsReadOutOfAndNotWhatItIsCalled() {
        Set<String> places = placesInTheDocument(model(Shape.FLAT, TWO_TABLES));
        assertEquals(2, places.size(), places.toString());
        assertTrue(places.stream().noneMatch(each -> each.contains("(")), places.toString());
        Set<String> aliased = placesInTheDocument(model(Shape.FLAT,
                "{ let alias = first\n        if useFirst then gradeIn(first, a.v)"
                        + " else gradeIn(alias, a.v) }"));
        assertEquals(1, aliased.size(), aliased.toString());
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
