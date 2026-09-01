package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceNameResolver;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the JSON writes where a measure has no value, and what it goes on writing beside it.
 *
 * <p>The specification says a measure with no number writes none — not a nought, not an empty set —
 * and two writers went on writing both: {@code branch} put {@code arms: 0} beside a status saying no
 * measurement was made, and a border's point put {@code hit: false} at a place nothing had looked at
 * (issue #997). A consumer dividing {@code covered} by {@code arms} got a measurement out of a
 * measure that does not apply.
 *
 * <p><b>Both directions, because the change is what absence means.</b> Making a key disappear is
 * only worth anything if the key is still there when the measurement is: absence would otherwise be
 * the answer to every question, and a reader could not tell a document that stopped writing
 * {@code hit} from one whose measure came back with nothing. So each case here is asserted against
 * its opposite in the same document.
 *
 * <p><b>And what stays.</b> {@code knownWritable} is not this measurement's answer — a row at the
 * point, a value built through the module's decoders and the rules proving the point inhabited each
 * settle it, and only the first is coverage — so it is written whether or not anybody measured. A
 * point nobody measured whose rules prove it inhabited carries {@code true} beside a status of
 * {@code unavailable}, and the two say different things about different questions.
 */
class AMeasureWithNoValueWritesNoFieldOfOneTest {

    /**
     * A behavior whose model draws two lines and whose body is never made.
     *
     * <p>The bound of {@code Amount} is a line a row meets by writing the value, so it is measured
     * without the arms. The {@code guard} draws one at 100 that a row meets by reaching the
     * comparison, so at a level that does not run instrumented rows it is not. The two live in one
     * document, which is what lets the same run show a key present and absent for the same reason.
     */
    private static final String MODEL = """
            module example.trip

            data Amount = Int
                invariant value >= 0

            data Draft = { cost: Amount }
            data Submitted = { cost: Amount }
            data Waiting = { cost: Amount }

            behavior submit : (request: Draft) -> Submitted | Waiting
                constructs Submitted, Waiting

            let submit (request) = {
                guard request.cost.value <= 100 else Waiting { cost = request.cost }
                Submitted { cost = request.cost }
            }

            example submit
                | (Draft { cost = Amount(50) }) -> Submitted
            """;

    /** The same model with a behavior the outside world implements, which has no body for the arm
     *  measure to be about. */
    private static final String INJECTED = MODEL + """

            data Receipt = { cost: Amount }

            behavior record : (of: Submitted) -> Receipt
            """;

    private static JsonNode reportOf(String source, Adequacy.Level level) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.reportOnly(level));
        compilation.answerEverything();
        JsonNode root = JsonMapper.builder().build().readTree(
                AdequacyReport.of(compilation).json(SourceNameResolver.identity()));
        assertNotNull(root, "the model under test compiles");
        return root;
    }

    private static JsonNode behavior(JsonNode report, String name) {
        for (JsonNode module : report.get("modules")) {
            for (JsonNode each : module.get("behaviors")) {
                if (name.equals(each.get("name").asString())) {
                    return each;
                }
            }
        }
        throw new AssertionError("no behavior " + name + " in " + report);
    }

    /** The point of one of the borders, whichever role, that has the status asked for. */
    private static JsonNode pointWithStatus(JsonNode behavior, String status) {
        for (JsonNode border : behavior.get("partition").get("boundaries")) {
            for (JsonNode point : border.get("items")) {
                if (point.has("status") && status.equals(point.get("status").asString())) {
                    return point;
                }
            }
        }
        throw new AssertionError("no point at " + status + " in " + behavior.get("partition"));
    }

    /**
     * A point nothing looked at says so, and says nothing about whether a row is there.
     *
     * <p>What is left is the two halves of what the point asks for — the relation and what it is
     * against, which the model states — and the status saying why nobody answered it.
     */
    @Test
    void aPointNobodyMeasuredWritesNoHit() {
        JsonNode point = pointWithStatus(behavior(reportOf(MODEL, Adequacy.Level.WITNESS), "submit"),
                "unavailable");

        assertNull(point.get("hit"),
                () -> "no measurement, so no answer about a row being here: " + point);
        assertEquals("arms_not_asked", point.get("reason").asString());
        assertTrue(point.has("relation") && point.has("against"),
                () -> "what the model says about the point stands: " + point);
    }

    /**
     * And a point that was measured and missed writes {@code false}.
     *
     * <p>The half of this change that keeps the other half worth anything. If a measured miss also
     * went unwritten, the key would say nothing at all — present for a hit and absent for everything
     * else — and every consumer would be back to inferring a miss from a silence.
     */
    @Test
    void aPointMeasuredAndMissedWritesHitFalse() {
        JsonNode behavior = behavior(reportOf(MODEL, Adequacy.Level.WITNESS), "submit");
        boolean missed = false;
        boolean met = false;
        for (JsonNode border : behavior.get("partition").get("boundaries")) {
            for (JsonNode point : border.get("items")) {
                if (point.has("hit")) {
                    assertEquals("complete", point.get("status").asString(),
                            () -> "a hit is written where the measurement has a value: " + point);
                    missed |= !point.get("hit").asBoolean();
                    met |= point.get("hit").asBoolean();
                }
            }
        }
        assertTrue(missed, () -> "the one row writes 50, so the bound at 0 is missed: " + behavior);
        assertTrue(met, () -> "and the class it is in is reached: " + behavior);
    }

    /**
     * A point nobody measured whose rules prove it inhabited is still known to be writable.
     *
     * <p>The two questions kept apart, in the one document where mixing them would show. Coverage
     * asks whether a row was seen at the point and had no answer; writability asks whether one can
     * be written there and has three ways to say yes, only one of which is a row. Read as one, this
     * point would either lose the answer it has or claim the one it does not.
     */
    @Test
    void aPointNobodyMeasuredStillSaysWhetherARowCanBeWritten() {
        JsonNode point = pointWithStatus(behavior(reportOf(MODEL, Adequacy.Level.WITNESS), "submit"),
                "unavailable");

        assertTrue(point.has("knownWritable"),
                () -> "settled by the rules, which no measurement was needed for: " + point);
        assertTrue(point.get("knownWritable").asBoolean(),
                () -> "and the projection reaches this point: " + point);
    }

    /**
     * A behavior with no body writes no arms, and nothing that is read beside them.
     *
     * <p>{@code denominatorSettled} goes with them although it is the account's answer about the
     * set rather than about any arm: what it qualifies is the arms, and a word beside no arms is an
     * answer standing in for a measurement nobody made.
     */
    @Test
    void aBehaviorWithNoBodyWritesNoArmCount() {
        JsonNode branch = behavior(reportOf(INJECTED, Adequacy.Level.ALL), "record").get("branch");

        assertEquals("unavailable", branch.get("status").asString());
        assertEquals("no_body", branch.get("reason").asString());
        for (String key : new String[] {"obligations", "denominatorSettled"}) {
            assertNull(branch.get(key), () -> key + " is a measurement nobody made: " + branch);
        }
    }

    /** And a behavior whose arms were counted writes each of them, with what it came to. */
    @Test
    void aBehaviorWhoseArmsWereCountedWritesThem() {
        JsonNode branch = behavior(reportOf(INJECTED, Adequacy.Level.ALL), "submit").get("branch");

        assertEquals("complete", branch.get("status").asString());
        assertEquals(2, branch.get("obligations").size());
        assertTrue(branch.get("denominatorSettled").asBoolean(),
                () -> "nothing has shown the arms to be short of one: " + branch);
        List<String> dispositions = new java.util.ArrayList<>();
        branch.get("obligations")
                .forEach(arm -> dispositions.add(arm.get("disposition").asString()));
        assertEquals(List.of("met", "unmet"), dispositions,
                () -> "the one row takes the guard's continued arm and not its else: " + branch);
    }

    /**
     * And what the shipped schema says about all this is true of what the writer writes.
     *
     * <p>Its own test because nothing else checks it. The walk that holds the schema and the writer
     * together reads a composition's branches for the keys they allow and never for what they
     * require, and says so — so an {@code if}/{@code then} added to the schema is a sentence nothing
     * enforces, and a wrong one would sit there being read by consumers. The two conditions this
     * change added are read out of the file and applied here, over a document holding both sides of
     * each of them.
     *
     * <p>Read from the schema rather than restated. A condition written here as well would be the
     * same decision in two files, which is what the shipped schema and this compiler's writers were
     * before anybody walked them together.
     */
    @Test
    void theConditionsTheSchemaStatesAreTrueOfWhatIsWritten() {
        JsonNode schema = schema();
        JsonNode report = reportOf(INJECTED, Adequacy.Level.WITNESS);

        JsonNode branches = schema.get("$defs").get("branch");
        int checked = 0;
        for (JsonNode module : report.get("modules")) {
            for (JsonNode each : module.get("behaviors")) {
                if (each.has("branch")) {
                    holds(branches, each.get("branch"));
                    checked++;
                }
            }
        }
        assertTrue(checked >= 2, "both a measured branch and an unmeasured one are in this report");

        JsonNode items = schema.get("$defs").get("partition").get("properties").get("boundaries")
                .get("items").get("properties").get("items").get("items");
        int measured = 0;
        int not = 0;
        for (JsonNode module : report.get("modules")) {
            for (JsonNode each : module.get("behaviors")) {
                if (!each.has("partition")) {
                    continue;
                }
                for (JsonNode border : each.get("partition").get("boundaries")) {
                    for (JsonNode point : border.get("items")) {
                        holds(items, point);
                        if (point.has("status")) {
                            boolean withAValue = List.of("complete", "partial")
                                    .contains(point.get("status").asString());
                            measured += withAValue ? 1 : 0;
                            not += withAValue ? 0 : 1;
                        }
                    }
                }
            }
        }
        // Both sides of the condition, in the one document. The corpus checked in beside this has no
        // point at a status with no value, so a check run over that alone would be a check on the
        // half of the condition that was already true (issue #997).
        int withAValue = measured;
        int without = not;
        assertTrue(withAValue > 0 && without > 0,
                () -> "the level was chosen so that both arms occur: " + withAValue + " measured, "
                        + without + " not");
    }

    /** The {@code if}/{@code then}/{@code else} of one object, applied to one document node. */
    private static void holds(JsonNode declared, JsonNode written) {
        boolean guard = true;
        for (String key : declared.get("if").get("properties").propertyNames()) {
            JsonNode words = declared.get("if").get("properties").get(key).get("enum");
            boolean here = written.has(key) && anyIs(words, written.get(key).asString());
            guard &= here;
        }
        for (String required : declared.get("if").has("required")
                ? names(declared.get("if").get("required")) : List.<String>of()) {
            guard &= written.has(required);
        }
        JsonNode taken = declared.get(guard ? "then" : "else");
        for (String key : required(taken)) {
            assertTrue(written.has(key),
                    () -> "the schema requires " + key + " here and it is not written: " + written);
        }
        for (String key : forbidden(taken)) {
            assertFalse(written.has(key),
                    () -> "the schema forbids " + key + " here and it is written: " + written);
        }
    }

    private static boolean anyIs(JsonNode words, String word) {
        for (JsonNode each : words) {
            if (word.equals(each.asString())) {
                return true;
            }
        }
        return false;
    }

    private static List<String> names(JsonNode array) {
        List<String> out = new java.util.ArrayList<>();
        for (JsonNode each : array) {
            out.add(each.asString());
        }
        return out;
    }

    private static List<String> required(JsonNode of) {
        return of != null && of.has("required") ? names(of.get("required")) : List.of();
    }

    /**
     * The keys a branch of the condition writes out of the document, however it spells it.
     *
     * <p>Two spellings because two conditions needed two: one key is {@code not: {required: [k]}}
     * and several are {@code not: {anyOf: [{required: [k]}, ...]}}. A reader of this that understood
     * only one of them would pass over the other in silence, which is the failure it is here to
     * catch, so meeting anything else is a failure rather than something skipped.
     */
    private static List<String> forbidden(JsonNode of) {
        if (of == null || !of.has("not")) {
            return List.of();
        }
        JsonNode not = of.get("not");
        if (not.has("required")) {
            return names(not.get("required"));
        }
        assertTrue(not.has("anyOf"), () -> "a refusal spelled a way this does not read: " + not);
        List<String> out = new java.util.ArrayList<>();
        for (JsonNode each : not.get("anyOf")) {
            assertTrue(each.has("required") && each.size() == 1,
                    () -> "a refusal spelled a way this does not read: " + each);
            out.addAll(names(each.get("required")));
        }
        return out;
    }

    private static JsonNode schema() {
        try (java.io.InputStream in = AdequacyReport.class
                .getResourceAsStream(AdequacyReport.SCHEMA_RESOURCE)) {
            assertNotNull(in, AdequacyReport.SCHEMA_RESOURCE + " ships beside the compiler");
            return JsonMapper.builder().build().readTree(
                    new String(in.readAllBytes(), java.nio.charset.StandardCharsets.UTF_8));
        } catch (java.io.IOException e) {
            throw new java.io.UncheckedIOException(e);
        }
    }
}
