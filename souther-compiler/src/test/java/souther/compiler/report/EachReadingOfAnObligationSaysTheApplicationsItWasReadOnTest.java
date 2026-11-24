package souther.compiler.report;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import souther.compiler.ACompiledModel;
import souther.compiler.DocumentShape;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Each reading of an obligation says which applications of a closure it was read on, and an
 * obligation says of each call how many of its applications made some of its readings and how many
 * readings they made.
 *
 * <p>Held against what the model says each application compares: a fold's step over a table
 * written out compares the input with the row it was handed, so the reading at a row's value is the
 * reading of the application handed that row. Two counts beside the readings and not a product of
 * them: two applications reading the line at one place are one reading of both.
 */
class EachReadingOfAnObligationSaysTheApplicationsItWasReadOnTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static List<Integer> rows(int n) {
        List<Integer> out = new ArrayList<>();
        for (int at = 1; at <= n; at++) {
            out.add(10 * at);
        }
        return out;
    }

    private static String table(List<Integer> rows) {
        return String.join(", ", rows.stream().map(String::valueOf).toList());
    }

    private static JsonNode obligations(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.OFF));
        ACompiledModel.compiles(compilation);
        JsonNode document = JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
        DocumentShape.assertShapedLikeTheSchema(document);
        return document.path("modules").get(0).path("behaviors").get(0).path("partition")
                .path("obligations");
    }

    /** The application of the one call each of {@code reading}'s applications is, by ordinal. */
    private static List<Integer> ordinals(JsonNode reading) {
        List<Integer> out = new ArrayList<>();
        for (JsonNode application : reading.path("applications")) {
            assertEquals(1, application.path("madeBy").size(), "one call made it: " + reading);
            out.add(application.path("madeBy").get(0).path("application").asInt());
        }
        return out;
    }

    /**
     * Which copy of the helper a call stands in, by which call of the helper made it: nothing for
     * a call written in the behavior.
     */
    private static String copy(JsonNode call) {
        return call.path("call").path("through").toString();
    }

    @Test
    void aFoldsStepOverATableIsReadOnceOnEachApplicationAtEachPoint() {
        for (int n : new int[]{3, 6, 9, 12}) {
            List<Integer> rows = rows(n);
            JsonNode obligations = obligations("""
                    module demo exposing (g)

                    behavior g : (x: Int) -> Int
                    let g (x) = List.fold((acc, r) -> if x >= r then acc + 1 else acc, 0, [ROWS])
                    """.replace("ROWS", table(rows)));
            assertEquals(4, obligations.size(), "one line, four points: " + obligations);
            for (JsonNode point : obligations) {
                JsonNode readings = point.path("readings");
                assertEquals(n, readings.size(), "a reading for each row: " + point);
                Set<Integer> made = new HashSet<>();
                for (JsonNode reading : readings) {
                    List<Integer> ordinal = ordinals(reading);
                    assertEquals(1, ordinal.size(), "one application read it: " + reading);
                    made.add(ordinal.getFirst());
                    // The application handed row r compares the input with r, which is where the
                    // line it reads stands.
                    int r = rows.get(ordinal.getFirst());
                    if (point.path("point").asString().equals("on")) {
                        assertEquals(String.valueOf(r), reading.path("against").asString());
                    }
                    if (point.path("point").asString().equals("off")) {
                        assertEquals(String.valueOf(r - 1), reading.path("against").asString());
                    }
                }
                assertEquals(n, made.size(), "every application read one of them: " + point);
                JsonNode byCall = point.path("readingsByCall");
                assertEquals(1, byCall.size(), "one call: " + point);
                assertEquals("List.fold", byCall.get(0).path("operation").asString());
                assertEquals(n, byCall.get(0).path("applications").asInt());
                assertEquals(n, byCall.get(0).path("readings").asInt());
                assertFalse(byCall.get(0).path("at").isMissingNode(),
                        "where the author wrote the call: " + byCall);
            }
        }
    }

    /** A helper called twice is two calls of the fold, each a copy of it, and each read on its
     *  own input. */
    @Test
    void aHelperCalledTwiceIsTwoCallsWhoseApplicationsMadeTwiceTheReadings() {
        for (int n : new int[]{3, 6, 9, 12}) {
            JsonNode obligations = obligations("""
                    module demo exposing (g)

                    let count (x: Int) : Int =
                        List.fold((acc, r) -> if x >= r then acc + 1 else acc, 0, [ROWS])

                    behavior g : (x: Int, y: Int) -> Int
                    let g (x, y) = count(x) + count(y)
                    """.replace("ROWS", table(rows(n))));
            for (JsonNode point : obligations) {
                assertEquals(2 * n, point.path("readings").size(), "of each call: " + point);
                JsonNode byCall = point.path("readingsByCall");
                assertEquals(2, byCall.size(), "two calls: " + point);
                assertFalse(copy(byCall.get(0)).equals(copy(byCall.get(1))),
                        "the copies of the two calls of the helper: " + byCall);
                for (JsonNode call : byCall) {
                    assertEquals(n, call.path("applications").asInt());
                    assertEquals(n, call.path("readings").asInt());
                }
                // Each reading is of the input its call was handed.
                for (JsonNode reading : point.path("readings")) {
                    String through = reading.path("applications").get(0).path("madeBy").get(0)
                            .path("call").path("through").get(0).path("call").toString();
                    assertEquals(reading.path("axis").asString().equals("g/x") ? "0" : "1",
                            through, reading.toString());
                }
            }
        }
    }

    @Test
    void twoApplicationsReadingTheSameTargetAreOneReadingOfBoth() {
        JsonNode obligations = obligations("""
                module demo exposing (g)

                behavior g : (x: Int) -> Int
                let g (x) = List.fold((acc, r) -> if x >= 10 then acc + r else acc, 0, [1, 2])
                """);
        assertEquals(4, obligations.size(), obligations.toString());
        for (JsonNode point : obligations) {
            assertEquals(1, point.path("readings").size(), point.toString());
            assertEquals(List.of(0, 1), ordinals(point.path("readings").get(0)), point.toString());
            JsonNode byCall = point.path("readingsByCall").get(0);
            assertEquals(2, byCall.path("applications").asInt(), byCall.toString());
            assertEquals(1, byCall.path("readings").asInt(), byCall.toString());
        }
    }

    /** Two calls of a helper on one input read one line at one place, and the reading they are
     *  put together as is read on the applications of both. */
    @Test
    void readingsPutTogetherAcrossTheCallsOfAHelperKeepTheApplicationsOfEach() {
        JsonNode obligations = obligations("""
                module demo exposing (g)

                let count (x: Int) : Int =
                    List.fold((acc, r) -> if x >= r then acc + 1 else acc, 0, [10, 20])

                behavior g : (x: Int) -> Int
                let g (x) = count(x) + count(x)
                """);
        for (JsonNode point : obligations) {
            assertEquals(2, point.path("readings").size(), point.toString());
            for (JsonNode reading : point.path("readings")) {
                Set<String> copies = new HashSet<>();
                reading.path("applications").forEach(one ->
                        copies.add(copy(one.path("madeBy").get(0))));
                assertEquals(2, copies.size(), "an application of each call: " + reading);
            }
            for (JsonNode call : point.path("readingsByCall")) {
                assertEquals(2, call.path("applications").asInt(), call.toString());
                assertEquals(2, call.path("readings").asInt(), call.toString());
            }
        }
    }

    /** The inner fold's first application inside the outer one's first and inside its second are
     *  two applications of it, each read on its own. */
    @Test
    void anInnerApplicationIsToldApartByTheOuterOneItIsInside() {
        JsonNode obligations = obligations("""
                module demo exposing (g)

                behavior g : (x: Int) -> Int
                let g (x) = List.fold((acc, r) -> acc + List.fold((n, s) ->
                    if x >= r + s then n + 1 else n, 0, [1, 2]), 0, [10, 20])
                """);
        JsonNode on = null;
        for (JsonNode point : obligations) {
            if (point.path("point").asString().equals("on")) {
                on = point;
            }
        }
        assertTrue(on != null, obligations.toString());
        List<String> made = new ArrayList<>();
        for (JsonNode reading : on.path("readings")) {
            JsonNode by = reading.path("applications").get(0).path("madeBy");
            assertEquals(2, by.size(), "the outer call and the inner: " + reading);
            int outer = by.get(0).path("application").asInt();
            int inner = by.get(1).path("application").asInt();
            // x >= r + s, with r the outer row and s the inner.
            assertEquals(String.valueOf(List.of(10, 20).get(outer) + List.of(1, 2).get(inner)),
                    reading.path("against").asString());
            made.add(outer + "," + inner);
        }
        assertEquals(Set.of("0,0", "0,1", "1,0", "1,1"), Set.copyOf(made));
        JsonNode byCall = on.path("readingsByCall");
        assertEquals(2, byCall.size(), byCall.toString());
        assertEquals(2, byCall.get(0).path("applications").asInt(), "outer: " + byCall);
        assertEquals(4, byCall.get(1).path("applications").asInt(), "inner: " + byCall);
    }

    /**
     * An operation that stops at its first answer makes its second application only on a row the
     * first did not answer, which is below the line the first reads: the line is read on the first
     * application alone, though the second compares against the same number.
     */
    @Test
    void anApplicationMadeOnlyPastTheLineIsNotOneTheLineIsReadOn() {
        JsonNode obligations = obligations("""
                module demo exposing (g, Big, Yes, No)

                data Big = { threshold: Int }
                data Yes
                data No

                behavior g : (n: Int, c: Bool) -> Yes | No
                let g (n, c) = {
                        let ks = [ Big { threshold = 100000 }
                                 , if c then Big { threshold = 100000 }
                                   else Big { threshold = 100000 } ]
                        if List.any((k) -> n >= k.threshold, ks) then Yes else No
                    }
                """);
        boolean read = false;
        for (JsonNode point : obligations) {
            for (JsonNode reading : point.path("readings")) {
                if (reading.path("axis").asString().equals("g/n")) {
                    read = true;
                    assertEquals(List.of(0), ordinals(reading), reading.toString());
                }
            }
        }
        assertTrue(read, "the line on n is read: " + obligations);
    }

    /** Outside every closure, and inside one over the input whose applications are not said,
     *  a reading is read on nothing a source's call is named for. */
    @Test
    void aReadingReadOnceSaysNoApplication() {
        JsonNode obligations = obligations("""
                module demo exposing (g)

                behavior g : (x: Int, xs: List<Int>) -> Int
                let g (x, xs) = if x >= 5 then List.fold((acc, r) -> if r >= 3 then acc + 1
                    else acc, 0, xs) else 0
                """);
        assertEquals(8, obligations.size(), obligations.toString());
        for (JsonNode point : obligations) {
            assertTrue(point.path("readingsByCall").isMissingNode(), point.toString());
            for (JsonNode reading : point.path("readings")) {
                assertTrue(reading.path("applications").isMissingNode(), reading.toString());
            }
        }
    }
}
