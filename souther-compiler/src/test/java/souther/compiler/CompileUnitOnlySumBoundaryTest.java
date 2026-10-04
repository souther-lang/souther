package souther.compiler;

import net.unit8.raoh.Err;
import net.unit8.raoh.Issue;
import net.unit8.raoh.Ok;
import net.unit8.raoh.Result;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A sum all of whose cases are unit data carries nothing but which case it is, so it crosses the
 * boundary as that name — a bare string, the form every other serializer gives a fieldless
 * enumeration (serde, FSharp.SystemTextJson, Jackson, OpenAPI). Wrapping it in an object whose only
 * entry is the discriminator adds a level for nothing, and it is what kept such a sum out of key
 * position: a JSON object's key cannot be an object (issue #161, ADR-0040).
 */
class CompileUnitOnlySumBoundaryTest {

    private static final String STAGE_FIELD = """
            module demo

            data Stage = Prospecting | Won | Lost
            data In = { stage: Stage }
            data Out = { stage: Stage }

            behavior run : (i: In) -> Out constructs Out

            let run (i) = Out { stage = i.stage }
            """;

    private static Object run(BytesClassLoader loader, String in, String out, Object raw)
            throws Exception {
        Object decoded = Codecs.decoded(loader, in, raw);
        Object behavior = Emitted.behavior(loader, "demo", "run").getConstructor().newInstance();
        return Codecs.encode(loader, out, Codecs.apply(behavior, decoded));
    }

    @Test
    void aUnitOnlySumInAFieldIsABareString() throws Exception {
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(STAGE_FIELD), getClass().getClassLoader());

        assertEquals(Map.of("stage", "Won"),
                run(loader, "demo.In", "demo.Out", Map.of("stage", "Won")));
    }

    @Test
    void aUnitOnlySumKeysAMapAcrossTheBoundary() throws Exception {
        String src = """
                module demo

                data Stage = Prospecting | Won | Lost
                data In = { n: Int }
                data Out = { byStage: Map<Stage, Int> }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out { byStage = Map.singleton(Won, i.n) }
                """;
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());

        assertEquals(Map.of("byStage", Map.of("Won", 3L)),
                run(loader, "demo.In", "demo.Out", Map.of("n", 3L)));
    }

    @Test
    void aKeyNoCaseAnswersToFailsAtTheKeyAsANameInAFieldDoes() throws Exception {
        String src = """
                module demo

                data Stage = Prospecting | Won | Lost
                data In = { byStage: Map<Stage, Int> }
                data Out = { n: Int }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out { n = Map.size(i.byStage) }
                """;
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());
        JsonNode node = JsonMapper.builder().build().readTree("{\"byStage\":{\"Closed\":1}}");

        // One rule, so one issue whether the name stands in a field or keys a map: only where it is
        // reported differs.
        for (Result<?> read : List.of(
                Codecs.decode(loader, "demo.In", Map.of("byStage", Map.of("Closed", 1L))),
                Codecs.decode(loader, "demo.In", "jsonDecoder", node))) {
            List<Issue> issues = assertInstanceOf(Err.class, read).issues().asList();

            assertEquals(1, issues.size(), issues.toString());
            Issue issue = issues.get(0);
            assertEquals("/byStage/Closed", issue.path().toString());
            assertEquals("not_allowed", issue.code());
            assertEquals(Map.of("allowed", List.of("Lost", "Prospecting", "Won"), "actual", "Closed"),
                    issue.meta());
        }
    }

    @Test
    void anExampleWritesAnEnumerationCaseByName() {
        String src = """
                module demo

                data Stage = Prospecting | Won | Lost
                data In = { stage: Stage }
                data Out = { won: Bool }

                behavior run : (i: In) -> Out constructs Out

                let run (i) =
                    Out { won = match i.stage with
                                    | Won -> true
                                    | Prospecting -> false
                                    | Lost -> false }

                example run
                    | "a won deal is won" : (In { stage = Won }) -> Out { won = true }
                    | "a lost deal is not" : (In { stage = Lost }) -> Out { won = false }
                """;

        // the fixture is built through the same neutral form the boundary uses, so a unit case that
        // belongs to an enumeration has to be written there as its name, not as a tagged object
        assertDoesNotThrow(() -> Compiler.compile(src));
    }

    /**
     * A unit data may be a case of an enumeration and of a sum that has a field-bearing case, and the
     * two travel differently. Which form a fixture writes is decided by the type of the position it
     * is written in, not by what other sums happen to list the case.
     */
    private static final String OPEN_IN_TWO_SUMS = """
            module demo

            data Open
            data Closed
            data Failed = { reason: String }
            data State = Open | Closed
            data Outcome = Open | Failed

            data In = { state: State }
            data Attempt = { outcome: Outcome }
            data Out = { ok: Bool }

            behavior run : (i: In) -> Out constructs Out

            let run (i) =
                Out { ok = match i.state with
                               | Open -> true
                               | Closed -> false }
            """;

    @Test
    void aFixtureWritesTheFormTheFieldsTypeReads() {
        String src = OPEN_IN_TWO_SUMS + """

                example run
                    | "an open state is open" : (In { state = Open }) -> Out { ok = true }
                    | "a closed one is not" : (In { state = Closed }) -> Out { ok = false }
                """;

        assertDoesNotThrow(() -> Compiler.compile(src));
    }

    @Test
    void theSameCaseInASumThatHasAFieldBearingCaseKeepsTheObject() throws Exception {
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(OPEN_IN_TWO_SUMS), getClass().getClassLoader());

        // Outcome has a field-bearing case, so it stays an object with the discriminator; State, whose
        // cases are all unit data, is the bare name — the same `Open` in both
        assertInstanceOf(Ok.class,
                Codecs.decode(loader, "demo.Attempt", Map.of("outcome", Map.of("type", "Open"))));
        assertInstanceOf(Ok.class, Codecs.decode(loader, "demo.In", Map.of("state", "Open")));
    }

    @Test
    void theJsonDecoderReadsTheSameBareString() throws Exception {
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(STAGE_FIELD), getClass().getClassLoader());
        JsonNode node = JsonMapper.builder().build().readTree("{\"stage\":\"Lost\"}");

        assertInstanceOf(Ok.class, Codecs.decode(loader, "demo.In", "jsonDecoder", node));
    }

    @Test
    void aNameNoCaseAnswersToFailsTheDecodeAsRaohsOneOfDoes() throws Exception {
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(STAGE_FIELD), getClass().getClassLoader());

        // A name is compared exactly, case and all, which is the rule Raoh's `oneOf` over strings
        // states and not the one its `enum` does: that folds ASCII case and would read `won`.
        for (String written : List.of("Closed", "won")) {
            Result<?> read = Codecs.decode(loader, "demo.In", Map.of("stage", written));
            List<Issue> issues = assertInstanceOf(Err.class, read).issues().asList();

            assertEquals(1, issues.size(), written);
            Issue issue = issues.get(0);
            assertEquals("/stage", issue.path().toString(), written);
            assertEquals("not_allowed", issue.code(), written);
            assertEquals("not_allowed", issue.messageKey(), written);
            assertEquals(Map.of("allowed", List.of("Lost", "Prospecting", "Won"), "actual", written),
                    issue.meta(), written);
        }
    }

    @Test
    void theNamesARefusalAllowsAreInCodePointOrder() throws Exception {
        // U+FF21 is before U+1D400, and `String` puts the second first: its high surrogate, U+D835,
        // is below U+FF21. Raoh lists what a value may be in code point order.
        String src = """
                module demo

                data Ａlpha
                data 𝐀lpha
                data Mark = 𝐀lpha | Ａlpha
                data In = { mark: Mark }
                data Out = { mark: Mark }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out { mark = i.mark }
                """;
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());

        Result<?> read = Codecs.decode(loader, "demo.In", Map.of("mark", "Beta"));
        Issue issue = assertInstanceOf(Err.class, read).issues().asList().get(0);

        assertEquals(List.of("Ａlpha", "𝐀lpha"), issue.meta().get("allowed"));
    }

    @Test
    void aSumWithOneFieldBearingCaseKeepsTheDiscriminatorObject() throws Exception {
        String src = """
                module demo

                data Won = { amount: Int }
                data Stage = Prospecting | Won
                data In = { stage: Stage }
                data Out = { stage: Stage }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out { stage = i.stage }
                """;
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());

        assertEquals(Map.of("stage", Map.of("type", "Prospecting")),
                run(loader, "demo.In", "demo.Out", Map.of("stage", Map.of("type", "Prospecting"))));
    }
}
