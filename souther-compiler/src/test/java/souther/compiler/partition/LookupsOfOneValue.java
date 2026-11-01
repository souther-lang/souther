package souther.compiler.partition;

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

/**
 * A model looking the average of fifteen amounts up in a table of grades, the way an occasional
 * revision of a grade does: the grade the average comes to is tested against the current one, and
 * where it is two or more away the average is looked up again.
 */
final class LookupsOfOneValue {

    private static final String SOURCE = """
            module demo

            data Yen = Int
                invariant value >= 0
            data Pay = { a: Yen, b: Yen, c: Yen, d: Yen, e: Yen }
                invariant a.value <= 1000000000000
                invariant b.value <= 1000000000000
                invariant c.value <= 1000000000000
                invariant d.value <= 1000000000000
                invariant e.value <= 1000000000000
            data Window = { first: Pay, second: Pay, third: Pay }
            data Row = { grade: Int, lowerBound: Yen }
            %s
            let table: List<Row> = [
            %s ]
            let totalOf (p: Pay): Yen = p.a + p.b + p.c + p.d + p.e
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
                [ 2 | Int.abs(computed - %s) < 2 ]

            behavior f : (current: Decision, w: Window) -> Decision | NotRequired
                constructs Decision, Row, Yen%s%s
            let f (current, w) = {
                let average = averageOf(monthsOf(w))
                %s
            }
            """;

    /**
     * What the behavior does with the average, and what it builds besides a decision, a row and
     * an amount.
     */
    enum Body {

        /** The grade the average comes to tested before it is looked up again. */
        TESTED_AGAIN("""
                let computed = gradeRowFor(average).grade
                    if NotRequired { reasons = blockers(current, w, computed) } as unchanged
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
    enum Grade {

        /** Any whole number. */
        UNBOUNDED("data Decision = { grade: Int }", "current.grade", "%s", ""),

        /** One grade for each row of the table, as a grade of social insurance is: a grade two
         *  or more from any one row's is one of them, where there are five or more, and none is
         *  two or more from every row's. */
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

    private LookupsOfOneValue() {}

    /** The model with {@code body} after the average, over a table of {@code rows} grades a
     *  thousand apart, a decision's grade any whole number. */
    static String model(Body body, int rows) {
        return model(body, Grade.UNBOUNDED, rows);
    }

    /** The same, a decision's grade what {@code grade} says. */
    static String model(Body body, Grade grade, int rows) {
        String table = IntStream.range(0, rows)
                .mapToObj(each -> "    Row { grade = %d, lowerBound = Yen(%d) }"
                        .formatted(each + 1, each * 1000))
                .collect(Collectors.joining(",\n"));
        return SOURCE.formatted(grade.declared.replace("ROWS", String.valueOf(rows)), table,
                grade.readOfTheCurrent,
                body.alsoConstructs, grade.alsoConstructs,
                body.text.replace("GRADE", grade.built.formatted("gradeRowFor(average).grade")));
    }

    /** The values of the average the lookup's borders are at, as the report of {@code source}
     *  says them. */
    static List<String> bordersOfTheLookup(String source) {
        return report(source).stream()
                .map(A_POINT_OF_THE_LOOKUP::matcher)
                .filter(Matcher::find)
                .map(found -> found.group(1))
                .sorted()
                .toList();
    }

    /** The report of {@code source}, line by line. */
    static List<String> report(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model under test compiles");
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts())).lines().toList();
    }

    /** The lines of the report of {@code source} saying something is not read. */
    static List<String> unread(String source) {
        return report(source).stream().filter(line -> line.contains("not read:")).toList();
    }
}
