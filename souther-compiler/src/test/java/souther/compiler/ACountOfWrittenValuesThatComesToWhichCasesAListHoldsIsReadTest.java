package souther.compiler;

import org.junit.jupiter.api.Test;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.Severity;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * How many of the values a list was written with a closure keeps, where what the closure states of
 * each value is which cases the elements of an input list are.
 *
 * <p>Two readings meet here. A choice all of whose arms state one thing states that thing, whichever
 * arm is taken: a world every clue lets stand is kept whatever the clues are, and the count comes to
 * a number beside how many of the other statements hold. And where the comparison of that count
 * comes to which cases the input's elements are, with no relation of numbers in it, it states what
 * {@code List.all} and {@code List.any} written over those cases would — no line, and no reading
 * that stopped, while what it tells apart is still owed rows.
 */
class ACountOfWrittenValuesThatComesToWhichCasesAListHoldsIsReadTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /** A world is kept where every clue holds of it, and a clue's case says which field it asks. */
    private static String model(String worlds, String rows) {
        return """
                module p
                import List ( filter, all, length )
                data W = { a: Int, b: Int }
                data IsA = { v: Int }
                data IsB = { v: Int }
                data Clue = IsA | IsB
                let worlds = [%s]
                behavior f : (clues: List<Clue>) -> Int
                let f (clues) = {
                    let fitting = filter(w -> all(c -> match c with
                        | IsA { v } -> w.a >= 1
                        | IsB { v } -> w.b >= 2, clues), worlds)
                    if length(fitting) == 1 then 1 else 2
                }
                example f
                %s
                """.formatted(worlds, rows);
    }

    /** What the measure of the one behavior came to, as the document writes it. */
    private record Measured(String status, List<JsonNode> findings) {

        /** The reason each place the comparison is filed at is left with, in the document's word. */
        List<String> leftByTheComparison() {
            List<String> out = new ArrayList<>();
            for (JsonNode each : findings) {
                if ("comparison".equals(each.path("ruleId").path("kind").asString(""))) {
                    out.add(each.path("reason").asString(""));
                }
            }
            return out;
        }

        /** The arms no row goes through. */
        List<String> unreached() {
            List<String> out = new ArrayList<>();
            for (JsonNode each : findings) {
                if ("arm_unreached".equals(each.get("kind").asString())) {
                    out.add(each.get("subject").asString());
                }
            }
            return out;
        }
    }

    private static Measured measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        JsonNode document = JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
        JsonNode behavior = document.get("modules").get(0).get("behaviors").get(0);
        List<JsonNode> findings = new ArrayList<>();
        behavior.path("findings").forEach(findings::add);
        return new Measured(behavior.get("status").asString(), findings);
    }

    /** The codes of the warnings a compile of {@code source} says. */
    private static List<String> warnings(String source) {
        return Compiler.compileWithWarnings(source).warnings().stream()
                .filter(each -> each.severity() == Severity.WARNING)
                .map(Diagnostic::code)
                .toList();
    }

    /**
     * Two of the three worlds are kept whatever the clues, and the third where none of them is an
     * {@code IsB}: two or three are kept, never one, so the comparison is settled and the arm under
     * it is one nothing reaches.
     *
     * <p>Each of the two worlds has both arms of the match holding, so what the closure states of a
     * clue there is that it holds, and not that it is one case or the other.
     */
    @Test
    void aWorldEveryArmKeepsIsKeptWhateverTheClues() {
        String source = model("W { a = 1, b = 2 }, W { a = 2, b = 3 }, W { a = 3, b = 1 }", """
                    | "a" : ([IsA { v = 1 }]) -> 2
                    | "b" : ([]) -> 2
                """);

        assertEquals(List.of("E1327"), warnings(source));
        assertEquals(List.of("rule_cuts_nothing", "rule_cuts_nothing"),
                measured(source).leftByTheComparison());
    }

    /**
     * One world kept whatever the clues, one where every clue is an {@code IsA} and one where every
     * clue is an {@code IsB}: exactly one is kept where the clues hold both cases. What the
     * comparison states is that some clue is not an {@code IsA} and some clue is not an
     * {@code IsB}, which is no relation of numbers, and with a row on each side the measure is whole.
     */
    @Test
    void aComparisonThatComesToWhichCasesTheCluesAreIsNoStop() {
        Measured measured = measured(model(
                "W { a = 1, b = 2 }, W { a = 2, b = 1 }, W { a = 0, b = 2 }", """
                    | "a" : ([IsA { v = 1 }]) -> 2
                    | "b" : ([]) -> 2
                    | "c" : ([IsA { v = 1 }, IsB { v = 1 }]) -> 1
                """));

        assertEquals("complete", measured.status());
        assertEquals(List.of(), measured.leftByTheComparison());
    }

    /** The same model without the row holding both cases: what the comparison tells apart is
     *  still owed a row, and the arm only that row reaches is the one no row goes through. */
    @Test
    void whatItTellsApartIsStillOwedARow() {
        Measured measured = measured(model(
                "W { a = 1, b = 2 }, W { a = 2, b = 1 }, W { a = 0, b = 2 }", """
                    | "a" : ([IsA { v = 1 }]) -> 2
                    | "b" : ([]) -> 2
                """));

        assertEquals(List.of(), measured.leftByTheComparison());
        assertTrue(measured.unreached().contains("then"), measured.unreached().toString());
    }

    /** One world, kept where every clue is an {@code IsA}: one statement about which cases the
     *  clues are, and no stop either. */
    @Test
    void oneStatementAboutTheCasesIsNoStopEither() {
        Measured measured = measured(model("W { a = 3, b = 1 }", """
                    | "a" : ([IsA { v = 1 }]) -> 1
                    | "b" : ([]) -> 1
                    | "c" : ([IsB { v = 1 }]) -> 2
                """));

        assertEquals("complete", measured.status());
        assertEquals(List.of(), measured.leftByTheComparison());
    }

    /**
     * The same count inside a closure applied to each world, over a list written with the one world
     * the closure was handed: on every application it comes to which cases the clues are, so the
     * comparison is no stop on any of them.
     *
     * <p>And the name the inner closure is handed is read where its value was written, the outer
     * closure's parameter, which no application handed anything there. Going into that parameter is
     * done once: handed again, it is met again where the inner name's value was written.
     */
    @Test
    void aComparisonReadOnEachApplicationThatComesToWhichCasesIsNoStop() {
        Measured measured = measured("""
                module p
                import List ( filter, all, any, length )
                data W = { a: Int, b: Int }
                data IsA = { v: Int }
                data IsB = { v: Int }
                data Clue = IsA | IsB
                let worlds = [W { a = 3, b = 1 }, W { a = 0, b = 2 }]
                behavior f : (clues: List<Clue>) -> Int
                let f (clues) =
                    if any(w -> length(filter(x -> all(c -> match c with
                        | IsA { v } -> x.a >= 1
                        | IsB { v } -> x.b >= 2, clues), [w])) == 1, worlds) then 1 else 2
                example f
                    | "a" : ([IsA { v = 1 }]) -> 1
                    | "b" : ([IsA { v = 1 }, IsB { v = 1 }]) -> 2
                """);

        assertEquals(List.of(), measured.leftByTheComparison());
    }

    /**
     * One comparison read on each value a closure is handed, where on one it comes to which cases
     * the clues are and on the other to what {@code onTheSecond} is compared as.
     */
    private static String readOnTwoApplications(String onTheSecond) {
        return """
                module p
                import List ( filter, any, length )
                data IsA = { v: Int }
                data IsB = { v: Int }
                data Clue = IsA | IsB
                behavior f : (clues: List<Clue>, n: Int) -> Int
                let f (clues, n) =
                    if any(k -> (if k == 1
                        then length(filter(c -> match c with
                            | IsA { v } -> true
                            | IsB { v } -> false, clues))
                        else %s) >= 1, [1, 2])
                    then 1
                    else 2
                example f
                    | "a" : ([IsA { v = 1 }], 0) -> 1
                    | "b" : ([], 0) -> 2
                    | "c" : ([], 3) -> 1
                """.formatted(onTheSecond);
    }

    /** A line on the other application: the statement holds a line and a part that is none, and
     *  the line drawn alone would be drawn as though the comparison were only it. */
    @Test
    void besideALineOnAnotherApplicationItIsSeveralLinesHeldTogether() {
        assertEquals(List.of("several_lines_in_one_rule", "several_lines_in_one_rule",
                        "several_lines_in_one_rule"),
                measured(readOnTwoApplications("n")).leftByTheComparison().stream()
                        .filter(each -> !each.isEmpty()).toList());
    }

    /** The same answer for every row on the other application: nothing beside the cases, and no
     *  stop. */
    @Test
    void besideAnApplicationSettledForEveryRowItIsNoStop() {
        assertEquals(List.of(), measured(readOnTwoApplications("5")).leftByTheComparison());
    }

    /** A form nothing reads on the other application: the reading stopped there, and that is what
     *  each place is told. */
    @Test
    void besideAnApplicationNothingReadTheStopIsWhatIsSaid() {
        assertEquals(List.of("non_affine_product", "non_affine_product", "non_affine_product"),
                measured(readOnTwoApplications("n * n")).leftByTheComparison().stream()
                        .filter(each -> !each.isEmpty()).toList());
    }

    /**
     * Ten worlds written as two, five times each: five kept is either the one or the other kept
     * and not both, which is two choices of which of two statements hold — and not one for each
     * way ten writings could come out, which is past the readings one condition is read in.
     */
    @Test
    void aStatementWrittenManyTimesIsOneStatementWeighedThatMany() {
        String worlds = String.join(", ", List.of(
                "W { a = 3, b = 1 }", "W { a = 0, b = 2 }", "W { a = 3, b = 1 }",
                "W { a = 0, b = 2 }", "W { a = 3, b = 1 }", "W { a = 0, b = 2 }",
                "W { a = 3, b = 1 }", "W { a = 0, b = 2 }", "W { a = 3, b = 1 }",
                "W { a = 0, b = 2 }"));
        Measured measured = measured(model(worlds, """
                    | "a" : ([IsA { v = 1 }]) -> 1
                    | "b" : ([IsB { v = 1 }]) -> 1
                    | "c" : ([]) -> 2
                    | "d" : ([IsA { v = 1 }, IsB { v = 1 }]) -> 2
                """).replace("length(fitting) == 1", "length(fitting) == 5"));

        assertEquals("complete", measured.status());

        assertEquals(List.of(), measured.leftByTheComparison());
    }

    /**
     * Some element meeting two matches over its cases is some element along one choice of each,
     * and a choice under one case for the first and under the other for the second is no element:
     * read as a way no element meets, and not a question about a number no row has. Asked as that
     * question, the measure ended in an exception and said nothing.
     *
     * <p>And each comparison of the second match is a line deciding where the element is in the
     * case its arm chose, which an element says of itself: the measure reads every rule.
     */
    @Test
    void aWayAskingAnElementToBeTwoCasesIsNoElement() {
        Measured measured = measured("""
                module p
                import List ( any )
                data A = { x: Int }
                data B = { y: Int }
                data C = A | B
                behavior f : (cs: List<C>) -> Int
                let f (cs) =
                    if any(c -> (match c with | A { x } -> x > 1 | B { y } -> y > 2)
                            && (match c with | A { x } -> x < 5 | B { y } -> y < 3), cs)
                    then 1
                    else 2
                example f
                    | "a" : ([A { x = 2 }]) -> 1
                    | "b" : ([]) -> 2
                """);

        assertEquals("complete", measured.status());
        assertTrue(measured.findings().stream().noneMatch(each ->
                        "several_lines_in_one_rule".equals(each.path("reason").asString(""))),
                () -> "every line is drawn: " + measured.findings());
    }

    /** A match whose arms both hold states that it holds, so a list every element of which meets
     *  it is every list, and the arm for one that does not is one nothing reaches. */
    @Test
    void aMatchWhoseArmsStateOneThingStatesIt() {
        String source = """
                module p
                import List ( all )
                data IsA = { v: Int }
                data IsB = { v: Int }
                data Clue = IsA | IsB
                behavior f : (clues: List<Clue>) -> Int
                let f (clues) =
                    if all(c -> match c with | IsA { v } -> true | IsB { v } -> true, clues)
                    then 1
                    else 2
                example f
                    | "a" : ([IsA { v = 1 }]) -> 1
                """;

        assertEquals(List.of("E1327"), warnings(source));
    }

    /**
     * Every seating of three suspects in some rooms, kept where every clue lets it stand, and
     * exactly one kept: with three rooms each placement a seating holds is asked about once per
     * seating, and exactly one of the seatings is more choices of which are kept, written out, than
     * a step is concluded with.
     */
    private static String seatings(String rooms) {
        return """
                module p
                import List ( flatMap, map, filter, all, any, length )
                data Suspect = Alice | Bob | Carol
                data Room = Kitchen | Study | Garden
                data Placement = { who: Suspect, room: Room }
                data SawIn = { who: Suspect, room: Room }
                data WasElsewhere = { who: Suspect, room: Room }
                data Clue = SawIn | WasElsewhere
                let rooms = [ %s ]
                let seatings =
                    flatMap(a -> flatMap(b -> map(c -> [ Placement { who = Alice, room = a }
                                                       , Placement { who = Bob, room = b }
                                                       , Placement { who = Carol, room = c } ],
                        rooms), rooms), rooms)
                let stood (places: List<Placement>, who: Suspect, room: Room): Bool =
                    any(p -> p.who == who && p.room == room, places)
                let holds (clue: Clue, places: List<Placement>): Bool =
                    match clue with
                        | SawIn { who, room } -> stood(places, who, room)
                        | WasElsewhere { who, room } -> Bool.not(stood(places, who, room))
                behavior solved : (clues: List<Clue>) -> Bool
                let solved (clues) = {
                    let fitting = filter(s -> all(clue -> holds(clue, s), clues), seatings)
                    length(fitting) == 1
                }
                example solved
                    | "one" : ([ SawIn { who = Alice, room = Study }, SawIn { who = Bob, room = Study }, SawIn { who = Carol, room = Study } ]) -> true
                    | "none" : ([ SawIn { who = Alice, room = Study }, WasElsewhere { who = Alice, room = Study } ]) -> false
                """.formatted(rooms);
    }

    /**
     * Exactly one of twenty-seven seatings is read to the end, as exactly one of eight is: the
     * count is held as the statements and the one count it admits, and a reader that takes it apart
     * is handed its choices. What is said of the clues is what is said where the choices are few
     * enough to be written out.
     */
    @Test
    void exactlyOneOfMoreSeatingsThanAreWrittenOutIsReadAsExactlyOneOfFewer() {
        Measured written = measured(seatings("Kitchen, Study"));
        Measured held = measured(seatings("Kitchen, Study, Garden"));

        assertEquals("complete", written.status());
        assertEquals("complete", held.status());
        assertEquals(kindsAndSubjects(written), kindsAndSubjects(held));
    }

    /**
     * Exactly nine of eighteen values written out, each a number of its own, is more choices than a
     * reader of them is handed: the count is read and held whole, and where its lines decide is
     * said not to have been worked out at that figure, and not that a part of it was not read.
     *
     * <p>Numbers of their own, since statements about one number cannot hold in most of the ways
     * a choice asks, and written out those ways are none.
     */
    @Test
    void aCountWhoseChoicesArePastWhatAReaderIsHandedSaysThatFigure() {
        String fields = IntStream.range(0, 18).mapToObj(at -> "f" + at + ": Int")
                .collect(Collectors.joining(", "));
        String values = IntStream.range(0, 18).mapToObj(at -> "w.f" + at)
                .collect(Collectors.joining(", ", "[", "]"));
        String zeros = IntStream.range(0, 18).mapToObj(at -> "f" + at + " = " + (at < 9 ? 1 : 0))
                .collect(Collectors.joining(", "));
        String source = """
                module p
                import List ( filter, length )
                data W = { %s }
                behavior f : (w: W) -> Int
                let f (w) = if length(filter(x -> x > 0, %s)) == 9 then 1 else 2
                example f
                    | "a" : (W { %s }) -> 1
                """.formatted(fields, values, zeros);
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String human = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));

        assertTrue(human.contains("PARTS_THE_CHOICES_OF_A_COUNT_COME_TO"), human);
        assertFalse(human.contains("a part of what it states was not read"), human);
    }

    /** Each finding's kind and what it is about. */
    private static List<String> kindsAndSubjects(Measured measured) {
        List<String> out = new ArrayList<>();
        for (JsonNode each : measured.findings()) {
            out.add(each.path("kind").asString("") + " " + each.path("subject").asString("")
                    + " " + each.path("reason").asString(""));
        }
        out.sort(String::compareTo);
        return out;
    }

    /** And an {@code if} whose arms state one thing, the same way. */
    @Test
    void anIfWhoseArmsStateOneThingStatesIt() {
        String source = """
                module p
                import List ( all )
                behavior f : (xs: List<Int>) -> Int
                let f (xs) =
                    if all(n -> if n > 0 then true else true, xs)
                    then 1
                    else 2
                example f
                    | "a" : ([1]) -> 1
                """;

        assertEquals(List.of("E1327"), warnings(source));
    }
}
