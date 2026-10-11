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

import static org.junit.jupiter.api.Assertions.assertEquals;
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
