package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.OfferedAtTheLines;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A total over a list of elements bounded on both sides takes what lists of more elements come
 * to, and not only what one element writes: two elements of nought to a hundred come to every
 * number up to two hundred. So a number compared with the total is reached past a hundred, and
 * rows are written there. Where the runs of one, two, three elements leave a gap between them, a
 * value in it is no total, and the number compared is not shown reached.
 */
class ATotalOfBoundedElementsReachesWhatSeveralElementsComeToTest {

    private static final String DECLARATIONS = """
            data Small = Int
                invariant value >= 0
                invariant value <= 100
            data S = { p: Small, q: Small }
            data ThreeOrFour = Int
                invariant value >= 3
                invariant value <= 4
            data G = { p: ThreeOrFour }
            data W = Int
            data Empty = { ls: List<S> }
                invariant List.length(ls) == 0
            data NoneButNeeded = { ls: List<S> }
                invariant List.length(ls) == 0 && List.any(l -> l.p.value > 0, ls)
            """;

    private static Compilation measured(String inputs, String body, Adequacy.Asked asked) {
        Compilation compilation = Compilation.ofSource("""
                module w1
                %s
                behavior m : (%s) -> Bool
                let m (%s) = %s
                """.formatted(DECLARATIONS, inputs,
                inputs.replaceAll(": (List<[^>]*>|[A-Za-z<>]+)", ""), body), "Main");
        compilation.measure(asked);
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model under test compiles");
        return compilation;
    }

    private static String report(String inputs, String body) {
        Compilation compilation = measured(inputs, body,
                Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static Set<String> related(String report) {
        return placesSaying(report, "· no line", "rather than dividing the values here");
    }

    private static Set<String> notShown(String report) {
        return placesSaying(report, "· not read", "not shown to reach every value here");
    }

    private static Set<String> placesSaying(String report, String start, String words) {
        return report.lines().map(String::strip)
                .filter(line -> line.startsWith(start) && line.contains(words))
                .map(line -> line.substring(line.lastIndexOf("about `") + 7, line.length() - 1))
                .collect(Collectors.toSet());
    }

    /**
     * The total of a field, a walk adding it, a walk taking another away, and a total of two
     * fields added, each over elements of nought to a hundred: the number compared is reached at
     * every value, as it is beside a total of elements with no greatest, and nothing is left
     * not shown.
     */
    @Test
    void aNumberComparedWithATotalOfBoundedElementsIsReached() {
        String inputs = "ls: List<S>, c: W";
        for (String[] each : List.of(
                new String[] {"List.sum(ls[*].p)",
                        "List.sum(List.map(l -> l.p.value, ls)) <= c.value"},
                new String[] {"List.sum(ls[*].p)",
                        "List.fold((acc, l) -> acc + l.p.value, 0, ls) <= c.value"},
                new String[] {"List.sum({-1·q + 0 | ls[*]})",
                        "List.fold((acc, l) -> acc - l.q.value, 0, ls) <= c.value"},
                new String[] {"List.sum({1·p + 1·q + 0 | ls[*]})",
                        "List.sum(List.map(l -> l.p.value + l.q.value, ls)) <= c.value"})) {
            String report = report(inputs, each[1]);
            assertEquals(Set.of(), notShown(report), () -> each[1] + report);
            assertEquals(Set.of(each[0]), related(report), () -> each[1] + report);
        }
    }

    /**
     * A walk that works the answer so far out twice in a step, {@code acc + p - q}, may pass the
     * type on the way where its answer does not, so its running totals are left untold and only
     * a row of one element is claimed ({@link UndividedByARelation.Working#partials}): what more
     * elements come to is not taken, and the number compared is not shown reached.
     */
    @Test
    void aWalkWhoseRunningTotalsAreUntoldIsTakenAtOneElement() {
        String report = report("ls: List<S>, c: W",
                "List.fold((acc, l) -> acc + l.p.value - l.q.value, 0, ls) <= c.value");
        assertEquals(Set.of("c"), notShown(report), report);
    }

    /** A list held to no element comes to nought, whatever its elements would come to, and the
     *  number compared is reached on both sides of it; held to none beside a rule that needs an
     *  element, it is no list a row is written at, and nothing is shown. */
    @Test
    void aTotalOfAContainerHoldingNoneIsNought() {
        String body = "List.sum(List.map(l -> l.p.value + l.q.value, b.ls)) <= c.value";
        String report = report("b: Empty, c: W", body);
        assertEquals(Set.of(), notShown(report), report);
        assertEquals(Set.of("List.sum({1·p + 1·q + 0 | b.ls[*]})"), related(report), report);
        String needing = report("b: NoneButNeeded, c: W", body);
        assertEquals(Set.of("List.sum({1·p + 1·q + 0 | b.ls[*]})", "c"), notShown(needing),
                needing);
    }

    /** Elements of three or four come to three or four, then six to eight, then nine on with no
     *  gap: five is no total, so the number compared is not shown reached at every value. */
    @Test
    void aGapBetweenTheTotalsOfTwoCountsIsNotReached() {
        String report = report("ls: List<G>, c: W",
                "List.sum(List.map(l -> l.p.value, ls)) <= c.value");
        assertEquals(Set.of("c"), notShown(report), report);
    }

    private static final Pattern ELEMENT =
            Pattern.compile("S \\{ p = Small\\((\\d+)\\), q = Small\\((\\d+)\\) }");

    /** Rows are written on both sides of a line past what one element writes, and each comes
     *  to what the point it is offered for names. */
    @Test
    void rowsAreWrittenPastWhatOneElementWrites() {
        assertWrittenAt("List.sum(List.map(l -> l.p.value, ls)) >= 150",
                "List.sum(ls[*].p)", List.of(150L, 149L), true);
        assertWrittenAt("List.fold((acc, l) -> acc - l.q.value, 0, ls) <= -150",
                "List.sum({-1·q + 0 | ls[*]})", List.of(-150L, -149L), false);
    }

    private static void assertWrittenAt(String body, String total, List<Long> points,
                                         boolean ofP) {
        Compilation compilation = measured("ls: List<S>", body, Adequacy.Asked.fullReport());
        Generator.GenerationResult offered = OfferedAtTheLines.of(compilation,
                compilation.modules().get(0), "m");
        List<Long> written = new ArrayList<>();
        for (Generator.GeneratedRow row : offered.rows()) {
            for (Generator.Purpose purpose : row.purposes()) {
                for (long at : points) {
                    if (purpose instanceof Generator.Purpose.ForAPoint point
                            && point.label().equals(total + " = " + at)) {
                        Matcher element = ELEMENT.matcher(row.inputs().getFirst().text());
                        long sum = 0;
                        int elements = 0;
                        while (element.find()) {
                            sum += ofP ? Long.parseLong(element.group(1))
                                    : -Long.parseLong(element.group(2));
                            elements++;
                        }
                        assertEquals(at, sum, row.inputs().getFirst()::text);
                        assertTrue(elements > 1, row.inputs().getFirst()::text);
                        written.add(at);
                    }
                }
            }
        }
        assertEquals(Set.copyOf(points), Set.copyOf(written), () -> body + " "
                + offered.unresolved());
        assertFalse(written.isEmpty());
    }
}
