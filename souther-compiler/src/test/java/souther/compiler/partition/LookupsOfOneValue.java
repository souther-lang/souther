package souther.compiler.partition;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;
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
            data Decision = { grade: Int }
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
                [ 2 | Int.abs(computed - current.grade) < 2 ]

            behavior f : (current: Decision, w: Window) -> Decision | NotRequired
                constructs Decision, Row, Yen%s
            let f (current, w) = {
                let average = averageOf(monthsOf(w))
                %s
            }
            """;

    /** The grade the average comes to tested before it is looked up again. */
    static final String TESTED_AGAIN = """
            let computed = gradeRowFor(average).grade
                if NotRequired { reasons = blockers(current, w, computed) } as unchanged
                then unchanged
                else Decision { grade = gradeRowFor(average).grade }""";

    /** The lookup with nothing before it. */
    static final String NOT_TESTED = """
            Decision { grade = gradeRowFor(average).grade }""";

    private LookupsOfOneValue() {}

    /** The model with {@code body} after the average, over a table of {@code rows} grades a
     *  thousand apart. */
    static String model(String body, int rows) {
        String table = IntStream.range(0, rows)
                .mapToObj(each -> "    Row { grade = %d, lowerBound = Yen(%d) }"
                        .formatted(each + 1, each * 1000))
                .collect(Collectors.joining(",\n"));
        return SOURCE.formatted(table, body.contains("NotRequired") ? ", NotRequired" : "", body);
    }

    /** What the report of {@code source} says about the comparisons of the table's lookup, with
     *  where in the source each stands left out: a line said of both lookups of the model that
     *  tests the grade is the line said of the one. */
    static List<String> aboutTheLookup(String source) {
        return report(source).stream().filter(line -> line.contains("gradeRowFor"))
                .map(line -> line.replaceAll("@\\d+:\\d+", "")
                        .replace("gradeRowFor, gradeRowFor", "gradeRowFor"))
                .sorted().toList();
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
