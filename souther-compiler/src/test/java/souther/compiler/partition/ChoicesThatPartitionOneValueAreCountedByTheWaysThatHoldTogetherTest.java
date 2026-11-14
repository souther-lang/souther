package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A lookup of the average in a table, after an {@code if} whose condition looks the same average
 * up in the same table, is read as it is with nothing before it.
 *
 * <p>The condition is read as two choices, each asking of the average and, apart from it, of the
 * grade the row found is compared with. Both part the average by the table's lines, so they hold
 * together only where they agree on the line, and are not as many ways as the product of their
 * sizes. And between them their alternatives leave the average every value, so they come to
 * nothing for the lookup after them.
 *
 * <p>The average is of two amounts, which is one form of more than one position, and the report
 * is asked at the level that reads the rows alone: what is said of a rule's line, and where the
 * lookup's borders are, is the model's and does not turn on where the rows went.
 */
class ChoicesThatPartitionOneValueAreCountedByTheWaysThatHoldTogetherTest {

    private static final String SOURCE = """
            module demo

            data Yen = Int
                invariant value >= 0 && value <= 1000000000000
            data Window = { first: Yen, second: Yen }
            data Row = { grade: Int, lowerBound: Yen }
            %s
            let table: List<Row> = [
            %s ]
            let gradeRowFor (m: Yen): Row =
                List.fold((acc, r) -> if r.lowerBound <= m then r else acc,
                          Row { grade = 0, lowerBound = Yen(0) }, table)
            let averageOf (records: List<Yen>): Yen =
                Yen(Rational.toInt(DOWN, List.sum(List.map(p -> p.value, records))
                    / List.length(records)))

            data NotRequired = { reasons: List<Int> }
                invariant List.length(reasons) >= 1
            let blockers (current: Decision, computed: Int): List<Int> =
                [ 2 | Int.abs(computed - %s) < 2 ]

            behavior f : (current: Decision, w: Window) -> Decision | NotRequired
                constructs Decision, Row, Yen%s%s
            let f (current, w) = {
                let average = averageOf([ w.first, w.second ])
                %s
            }
            """;

    /** What the behavior does with the average. */
    private enum Body {

        /** The grade the average comes to tested before it is looked up again. */
        TESTED_AGAIN("""
                let computed = gradeRowFor(average).grade
                    if NotRequired { reasons = blockers(current, computed) } as unchanged
                    then unchanged
                    else Decision { grade = GRADE }""", ", NotRequired"),

        /** The lookup with nothing before it. */
        NOT_TESTED("""
                Decision { grade = GRADE }""", "");

        private final String text;
        private final String alsoConstructs;

        Body(String text, String alsoConstructs) {
            this.text = text;
            this.alsoConstructs = alsoConstructs;
        }
    }

    /** What the grade of a decision is: any whole number, or one of so many grades. */
    private enum Grade {

        UNBOUNDED("data Decision = { grade: Int }", "current.grade", "%s", ""),

        /** One grade for each row of the table: a grade two or more from any one row's is one of
         *  them, and none is two or more from every row's. */
        ONE_FOR_EACH_ROW("""
                data Grade = Int
                    invariant value >= 1 && value <= ROWS
                data Decision = { grade: Grade }""", "current.grade.value", "Grade(%s)", ", Grade"),

        /** One of three grades: no grade is two or more from the middle row's. */
        ONE_OF_THREE("""
                data Grade = Int
                    invariant value >= 1 && value <= 3
                data Decision = { grade: Grade }""", "current.grade.value", "Grade(%s)", ", Grade");

        private final String declared;
        private final String readOfTheCurrent;
        private final String built;
        private final String alsoConstructs;

        Grade(String declared, String readOfTheCurrent, String built, String alsoConstructs) {
            this.declared = declared;
            this.readOfTheCurrent = readOfTheCurrent;
            this.built = built;
            this.alsoConstructs = alsoConstructs;
        }
    }

    private static final Pattern A_POINT_OF_THE_LOOKUP =
            Pattern.compile("read as f/.*: = (\\S+) in gradeRowFor");

    /** The model with {@code body} after the average, over a table of {@code rows} grades a
     *  thousand apart. */
    private static String model(Body body, Grade grade, int rows) {
        String table = IntStream.range(0, rows)
                .mapToObj(each -> "    Row { grade = %d, lowerBound = Yen(%d) }"
                        .formatted(each + 1, each * 1000))
                .collect(Collectors.joining(",\n"));
        return SOURCE.formatted(grade.declared.replace("ROWS", String.valueOf(rows)), table,
                grade.readOfTheCurrent, body.alsoConstructs, grade.alsoConstructs,
                body.text.replace("GRADE", grade.built.formatted("gradeRowFor(average).grade")));
    }

    /** The report of {@code source}, line by line. */
    private static List<String> report(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        ACompiledModel.compiles(compilation);
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts())).lines().toList();
    }

    /** The lines of {@code report} saying something is not read. */
    private static List<String> unreadIn(List<String> report) {
        return report.stream().filter(line -> line.contains("not read:")).toList();
    }

    /** The values of the average the lookup's borders are at, as {@code report} says them. */
    private static List<String> bordersIn(List<String> report) {
        return report.stream()
                .map(A_POINT_OF_THE_LOOKUP::matcher)
                .filter(Matcher::find)
                .map(found -> found.group(1))
                .sorted()
                .toList();
    }

    @Test
    void aLookupAfterAnIfLookingTheSameValueUpIsReadAsItIsWithNothingBeforeIt() {
        List<String> report = report(model(Body.TESTED_AGAIN, Grade.UNBOUNDED, 2));
        List<String> withNothingBefore =
                bordersIn(report(model(Body.NOT_TESTED, Grade.UNBOUNDED, 2)));

        assertEquals(List.of(), unreadIn(report));
        assertFalse(withNothingBefore.isEmpty(), "the lookup has borders to compare");
        assertEquals(withNothingBefore, bordersIn(report));
    }

    /**
     * The same where the grade compared with is one of a grade for each row: what each row asks
     * of it is a grade two or more from the row's, which some grade is for every row, and no
     * grade is for every row at once, nor for every row above or below the one taken. So each row
     * is met by a grade of its own and by no one grade.
     */
    @Test
    void aLookupAfterAnIfOverAGradeForEachRowIsRead() {
        assertEquals(List.of(),
                unreadIn(report(model(Body.TESTED_AGAIN, Grade.ONE_FOR_EACH_ROW, 4))));
    }

    /**
     * Control: where the grade is one of three, no grade is two or more from the middle row's,
     * so no row past the {@code if} has the average in the middle row's run, and the lookup after
     * it is not read as reaching every value.
     */
    @Test
    void aLookupAfterAnIfNoGradeGetsPastForSomeRowIsNotRead() {
        assertFalse(unreadIn(report(model(Body.TESTED_AGAIN, Grade.ONE_OF_THREE, 3))).isEmpty());
    }
}
