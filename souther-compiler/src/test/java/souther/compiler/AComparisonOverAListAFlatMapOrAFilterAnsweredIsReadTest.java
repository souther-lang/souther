package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.partition.WhatTheComparisonsState;
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
 * one it drops is no case the comparison names, and one it keeps is, whatever it is kept by.
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

    private static final String PLACED = """
            module p
            data Suspect = Alice | Bob | Carol
            data Placement = { who: Suspect, room: Int }
            let places = %s
            behavior f : (who: Suspect) -> Bool
            let f (who) = List.any(p -> p.who == who, places)
            example f
            %s""";

    private static String measured(String places, String rows) {
        return measured(PLACED.formatted(places, rows));
    }

    /**
     * What {@code f} states of who it is asked about, over {@code places}.
     *
     * <p>Each placement compares a case with the value, which asks which case it is and draws no
     * line: the cases the list holds are what says it was read.
     */
    private static String states(String places, String rows) {
        Compilation compilation = Compilation.ofSource(PLACED.formatted(places, rows), "Main");
        compilation.answerEverything();
        List<String> out = WhatTheComparisonsState.of(compilation, "f");
        assertEquals(1, out.size(), () -> "one comparison is written: " + out);
        return out.getFirst();
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

    /** What the comparison states over a list holding Alice and Bob: the closure applied to each. */
    private static final String BOTH = "on an application[who is Alice, who is Bob]";

    /** What it states over a list holding Alice alone. */
    private static final String ALICE = "who is Alice";

    /** Control: the list written out is read, a case at each placement. */
    @Test
    void theListWrittenOutIsRead() {
        String report = measured(WRITTEN, BOTH_PLACED);
        assertEquals(List.of(), notRead(report));
        assertEquals(BOTH, states(WRITTEN, BOTH_PLACED), "who is one of the two placed");
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

    /** A filter dropping a placement leaves the case at it out; the one it keeps is a case. */
    @Test
    void aFilterIsReadAsTheElementsItKeeps() {
        String kept = "List.filter(p -> p.room == 1, [Placement { who = Alice,"
                + " room = 1 }, Placement { who = Bob, room = 2 }])";
        String report = measured(kept, ALICE_PLACED);
        assertEquals(List.of(), notRead(report));
        assertEquals(ALICE, states(kept, ALICE_PLACED), "only Alice is kept");
        assertTrue(report.contains("adequacy: satisfied"), report);
    }

    /** The same filter keeping both is a case at each: what made the difference is what it kept. */
    @Test
    void aFilterKeepingEveryElementIsACaseAtEach() {
        String kept = "List.filter(p -> p.room >= 1, [Placement { who = Alice,"
                + " room = 1 }, Placement { who = Bob, room = 2 }])";
        String report = measured(kept, BOTH_PLACED);
        assertEquals(List.of(), notRead(report));
        assertEquals(BOTH, states(kept, BOTH_PLACED), "both are kept");
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

    /**
     * A closure handed the elements of a list that holds none is applied by no run, so a comparison
     * inside it is no boundary — whether the list is written empty or put together of empty pieces.
     */
    @Test
    void aComparisonInAClosureAppliedToNothingIsNoLine() {
        for (String none : List.of("none", "List.flatMap(k -> none, [1])",
                "List.filter(k -> k > 5, [1])")) {
            String report = measured("""
                    module p
                    behavior f : (n: Int) -> Bool
                    let f (n) = {
                        let none: List<Int> = []
                        List.any(x -> n > 0, %s)
                    }
                    example f
                        | "a" : (1) -> false
                    """.formatted(none));
            assertEquals(List.of(), notRead(report), none);
            assertTrue(headed(report, "border").contains("not applicable"), report);
        }
    }

    /**
     * And so of an arm no application enters, every value handed being one whose part the arm
     * decides on is a case it does not take — which is known of each application and not of the
     * element read as all of them at once.
     */
    @Test
    void aComparisonInAnArmNoApplicationEntersIsNoLine() {
        String report = measured("""
                module p
                data Yes
                data No
                data Answer = Yes | No
                data Item = { answer: Answer }
                behavior f : (n: Int) -> Bool
                let f (n) = List.any(i -> match i.answer with
                                              | Yes -> n > 0
                                              | No -> false,
                                     [Item { answer = No }, Item { answer = No }])
                example f
                    | "a" : (1) -> false
                """);
        assertEquals(List.of(), notRead(report));
        assertTrue(headed(report, "border").contains("not applicable"), report);
    }

    /**
     * What a closure states of an element a filter drops is no part of what is read, and one that
     * cannot be read leaves the elements kept read: {@code n < n * n} is no line this compiler
     * draws, and no run compares it.
     */
    @Test
    void aComparisonOnAnElementDroppedOnEveryRowLeavesTheKeptOnesRead() {
        String report = measured("""
                module p
                data Item = { keep: Bool, value: Int }
                behavior f : (n: Int) -> Bool
                let f (n) = List.any(x -> n < x.value, List.filter(x -> x.keep,
                    [Item { keep = true, value = 1 }, Item { keep = false, value = n * n }]))
                example f
                    | "below" : (0) -> true
                    | "at" : (1) -> false
                """);
        assertEquals(List.of(), notRead(report));
        assertTrue(headed(report, "border").contains("borders 1"), report);
    }

    /** And so of an application no run makes because the walk has stopped before it on every
     *  row. */
    @Test
    void aComparisonOnAnApplicationAfterTheWalkStoppedIsNotRead() {
        String report = measured("""
                module p
                data Item = { keep: Bool, value: Int }
                behavior f : (n: Int) -> Bool
                let f (n) = List.any(x -> x.keep || n < x.value,
                    [Item { keep = true, value = 1 }, Item { keep = false, value = n * n }])
                example f
                    | "always" : (0) -> true
                """);
        assertEquals(List.of(), notRead(report));
    }

    /** And so where what it keeps by is which case the element is, either way round. */
    @Test
    void aFilterKeepingByACaseIsReadAsTheElementsItKeeps() {
        for (String keep : List.of("p.who == Alice", "p.who /= Bob")) {
            String kept = "List.filter(p -> " + keep + ", [Placement { who = Alice,"
                    + " room = 1 }, Placement { who = Bob, room = 2 }])";
            String report = measured(kept, ALICE_PLACED);
            assertEquals(List.of(), notRead(report), keep);
            assertEquals(ALICE, states(kept, ALICE_PLACED), keep);
        }
    }

    /**
     * How many a flatMap answers adds up what each element it is handed puts in, and of a filter
     * of values written out the elements are the ones it keeps: here two of the three, two each.
     */
    @Test
    void aSumOverTheElementsAFilterKeptAddsUpTheOnesItKept() {
        String report = measured("""
                module p
                behavior f : (n: Int) -> Bool
                let f (n) = n >= List.length(List.flatMap(w -> [w, w],
                                                          List.filter(w -> w >= 2, [1, 2, 3])))
                example f
                    | "below" : (3) -> false
                    | "at" : (4) -> true
                """);
        assertEquals(List.of(), notRead(report));
        assertTrue(report.contains("read as f/n: in 4 < n"), report);
        assertTrue(report.contains("read as f/n: in n < 3"), report);
    }

    /** One kept or not by what the row is makes the sum turn on the row, and it is not read as
     *  the sum of all of them. */
    @Test
    void aSumOverElementsKeptByTheRowIsNotReadAsASumOfThemAll() {
        String report = measured("""
                module p
                behavior f : (n: Int) -> Bool
                let f (n) = n >= List.length(List.flatMap(w -> [w, w],
                                                          List.filter(w -> w >= n, [1, 2, 3])))
                example f
                    | "below" : (0) -> false
                    | "at" : (6) -> true
                """);
        assertTrue(report.contains("not read: comparison@3:15"), report);
        assertTrue(headed(report, "border").contains("borders 3"),
                () -> "the filter's own comparison is read at each element: " + report);
    }
}
