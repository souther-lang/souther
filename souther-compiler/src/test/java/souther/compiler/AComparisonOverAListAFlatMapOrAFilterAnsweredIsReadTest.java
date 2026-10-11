package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison against an element of a list a flatMap or a filter answered is read as the
 * comparison against each element the list holds, as it is where the list is written out.
 *
 * <p>Asked of the report a person reads, over a value the module declares: the comparison is read
 * through the name to the definition, and the definition is a list these operations put together of
 * a list written out. Where the list a flatMap puts together is the list written out, the report is
 * the one the written list gets, line for line. A filter's report is about the elements it keeps:
 * one it drops is no line, and one it keeps is, whatever it is kept by.
 */
class AComparisonOverAListAFlatMapOrAFilterAnsweredIsReadTest {

    private static final String WRITTEN =
            "[Placement { who = Alice, room = 1 }, Placement { who = Bob, room = 1 }]";

    private static final String BOTH_PLACED = """
                | "a" : (Alice) -> true
                | "b" : (Bob) -> true
                | "c" : (Carol) -> false
            """;

    private static final String ALICE_PLACED = """
                | "a" : (Alice) -> true
                | "b" : (Bob) -> false
                | "c" : (Carol) -> false
            """;

    private static String measured(String places, String rows) {
        return measured("""
                module p
                data Suspect = Alice | Bob | Carol
                data Placement = { who: Suspect, room: Int }
                let places = %s
                behavior f : (who: Suspect) -> Bool
                let f (who) = List.any(p -> p.who == who, places)
                example f
                %s""".formatted(places, rows));
    }

    private static String measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model under test compiles");
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static List<String> notRead(String report) {
        return report.lines().filter(line -> line.contains("not read")
                || line.contains("not accounted for")).toList();
    }

    /** The line of the report that heads {@code section}. */
    private static String headed(String report, String section) {
        return report.lines().filter(line -> line.strip().startsWith(section + " "))
                .findFirst().orElse("no " + section + " in " + report);
    }

    /** Control: the list written out is read, a line at each placement. */
    @Test
    void theListWrittenOutIsRead() {
        String report = measured(WRITTEN, BOTH_PLACED);
        assertEquals(List.of(), notRead(report));
        assertTrue(headed(report, "border").contains("borders 2"), report);
    }

    @Test
    void aFlatMapIsReadAsTheListItPutsTogether() {
        String report = measured(
                "List.flatMap(s -> [Placement { who = s, room = 1 }], [Alice, Bob])",
                BOTH_PLACED);
        assertEquals(List.of(), notRead(report));
        assertEquals(measured(WRITTEN, BOTH_PLACED), report);
    }

    @Test
    void aFlatMapWhoseStepIsAMapIsReadAsTheListItPutsTogether() {
        String report = measured(
                "List.flatMap(s -> List.map(r -> Placement { who = s, room = r }, [1]),"
                        + " [Alice, Bob])",
                BOTH_PLACED);
        assertEquals(List.of(), notRead(report));
        assertEquals(measured(WRITTEN, BOTH_PLACED), report);
    }

    /** A filter dropping a placement leaves the line at it out; the one it keeps is a line. */
    @Test
    void aFilterIsReadAsTheElementsItKeeps() {
        String report = measured("List.filter(p -> p.room == 1, [Placement { who = Alice,"
                + " room = 1 }, Placement { who = Bob, room = 2 }])", ALICE_PLACED);
        assertEquals(List.of(), notRead(report));
        assertTrue(headed(report, "border").contains("borders 1"), report);
        assertTrue(report.contains("adequacy: satisfied"), report);
    }

    /** The same filter keeping both is a line at each: what made the difference is what it kept. */
    @Test
    void aFilterKeepingEveryElementIsALineAtEach() {
        String report = measured("List.filter(p -> p.room >= 1, [Placement { who = Alice,"
                + " room = 1 }, Placement { who = Bob, room = 2 }])", BOTH_PLACED);
        assertEquals(List.of(), notRead(report));
        assertTrue(headed(report, "border").contains("borders 2"), report);
    }

    /**
     * An element a filter dropped stops no walk. {@code List.any} stops at the first element its
     * closure holds of, and the one dropped here would hold of every row the kept one does: read as
     * though it were there, the kept one would be reached on no row its line decides.
     */
    @Test
    void anElementAFilterDroppedStopsNoWalk() {
        String report = measured("""
                module p
                data Big = { threshold: Int }
                let bigs = List.filter(b -> b.threshold >= 2,
                                       [Big { threshold = 1 }, Big { threshold = 2 }])
                behavior f : (n: Int) -> Bool
                let f (n) = List.any(b -> n >= b.threshold, bigs)
                example f
                    | "below" : (0) -> false
                    | "at" : (2) -> true
                """);
        assertEquals(List.of(), notRead(report));
        assertTrue(headed(report, "border").contains("borders 1"), report);
    }

    /** And so where what it keeps by is which case the element is, either way round. */
    @Test
    void aFilterKeepingByACaseIsReadAsTheElementsItKeeps() {
        for (String keep : List.of("p.who == Alice", "p.who /= Bob")) {
            String report = measured("List.filter(p -> " + keep + ", [Placement { who = Alice,"
                    + " room = 1 }, Placement { who = Bob, room = 2 }])", ALICE_PLACED);
            assertEquals(List.of(), notRead(report), keep);
            assertTrue(headed(report, "border").contains("borders 1"), report);
        }
    }
}
