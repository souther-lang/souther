package souther.compiler;

import org.junit.jupiter.api.Test;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A document that names a source by an identity says what that identity was.
 *
 * <p>The identity is what the report carries, and rightly: it is what two runs compare on, and a name
 * is chosen from the files in front of one reader and is neither stable nor a key. What follows is
 * that the document cannot be read by anyone who does not also hold what was handed to the compile —
 * a consumer given `+"subject": "1"+` and nothing else has no way to reach the file. So the
 * identities stay and the document explains them.
 *
 * <p>Held as a property of the document rather than as an expected value per field. A reason's
 * subject is one place an identity is written and a position that points into a source is another,
 * and what went wrong the first time was that a rule was carried out at the fields somebody had
 * listed. These read the document for identities wherever they are and ask that each one is
 * explained, so a field that comes to carry one is covered by the test that was already written.
 */
class ADocumentExplainsTheIdentitiesItCarriesTest {

    /** A model whose rows are never evaluated: the `constructs` clause promises a construction the
     * body does not make, which is raised before anything runs. Its report carries a reason about
     * the source, whose subject is that source's identity. */
    private static String stopped(String module, String type) {
        return String.format("""
                module %s

                data %s = Int
                    invariant value >= 0

                behavior passThrough : (a: %s) -> %s
                    constructs %s
                let passThrough (a) = a

                example passThrough
                    | "through" : (%s(1)) -> %s(1)
                """, module, type, type, type, type, type, type);
    }

    /** A model with an arm no row goes through, which is the other way an identity is written: the
     * arm is reported with where it is, and where is a position in a source. */
    private static final String ONE_ARM_UNREACHED = """
            module example.arms

            data Ok = { n: Int }

            behavior take : (v: Int) -> Ok
                constructs Ok

            let take (v) = if v > 10 then Ok { n = 1 } else Ok { n = 0 }

            example take
                | "over" : (20) -> Ok { n = 1 }
            """;

    /** A model that leaves nothing to say about a source: its rows run, and its body has no arms for
     * an unreached one to be reported at. */
    private static final String NOTHING_TO_SAY = """
            module example.plain

            data Ok = { n: Int }

            behavior keep : (v: Int) -> Ok
                constructs Ok

            let keep (v) = Ok { n = v }

            example keep
                | "one" : (1) -> Ok { n = 1 }
            """;

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /**
     * Every identity the document writes is one the document explains.
     *
     * <p>Both kinds are in this run on purpose: a reason about a source that could not be read, and a
     * position pointing at an arm nothing reached. They are written by different code and were
     * explained by neither.
     */
    @Test
    void everySourceIdentityWrittenHasAnEntry() throws Exception {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put("arms.sou", ONE_ARM_UNREACHED);
        sources.put("stopped.sou", stopped("example.stopped", "Qty"));

        JsonNode report = JSON.readTree(run(sources, "--format", "json").out());

        List<Written> written = identitiesIn(report, new ArrayList<>());
        assertTrue(written.stream().anyMatch(w -> w.field().equals("subject")),
                "a reason about a source is in this document: " + report);
        assertTrue(written.stream().anyMatch(w -> w.field().equals("sourceId")),
                "and so is a position that points into one: " + report);

        Set<String> explained = new LinkedHashSet<>(report.get("sources").propertyNames());
        for (Written each : written) {
            assertTrue(explained.contains(each.sourceId()),
                    each + " is written and not explained by " + explained);
        }
    }

    /**
     * And what it says a source is called is what the run says everywhere else.
     *
     * <p>Two files whose names collide, so that a resolver answering with the basename gives a
     * different answer from one answering with enough of the path. The report a person reads and the
     * diagnostics both name the file, and a document disagreeing with the terminal that produced it
     * is the thing this leaves no room for.
     */
    @Test
    void theNamesAreTheOnesTheRestOfTheRunUses() throws Exception {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put("a/model.sou", stopped("example.a", "Qty"));
        sources.put("b/model.sou", stopped("example.b", "Amount"));

        Streams asJson = run(sources, "--format", "json");
        Streams asText = run(sources);

        Map<String, String> table = new LinkedHashMap<>();
        JsonNode explained = JSON.readTree(asJson.out()).get("sources");
        for (String sourceId : explained.propertyNames()) {
            table.put(sourceId, explained.get(sourceId).asString());
        }
        assertEquals(Map.of("0", "a/model.sou", "1", "b/model.sou"), table, asJson.out());
        for (String name : table.values()) {
            assertTrue(asText.out().contains("no rows were read from `" + name + "`"),
                    "the report a person reads says " + name + ":\n" + asText.out());
            assertTrue(asJson.err().contains("\"file\":\"" + name + "\""),
                    "and so do the diagnostics of the same run:\n" + asJson.err());
        }
    }

    /**
     * What was handed to the compile is not what this says.
     *
     * <p>Three files and one of them written about. A table of everything given to the command would
     * be a second thing for this document to be about — what was compiled, beside what the rows
     * cover — and a consumer reading it as the report's subject would be reading in two files nothing
     * here says anything about.
     */
    @Test
    void aSourceTheReportSaysNothingAboutHasNoEntry() throws Exception {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put("plain.sou", NOTHING_TO_SAY);
        sources.put("stopped.sou", stopped("example.stopped", "Qty"));
        sources.put("quiet.sou", NOTHING_TO_SAY.replace("example.plain", "example.quiet"));

        JsonNode report = JSON.readTree(run(sources, "--format", "json").out());

        assertEquals(3, report.get("modules").size(), "all three were measured: " + report);
        assertEquals(List.of("1"), List.copyOf(report.get("sources").propertyNames()),
                "only the source something is said about: " + report);
        assertEquals("stopped.sou", report.get("sources").get("1").asString(), report.toString());
    }

    /** Where a source identity was written, and which one. */
    private record Written(String field, String sourceId) {}

    /**
     * The source identities anywhere in a document.
     *
     * <p>Read off what the schema says an identity is rather than off the places one is emitted
     * today: an `+at+` names its source under `+sourceId+` wherever an `+at+` sits, and a reason's
     * `+subject+` is one exactly where its `+scope+` says `+source+`. A field added later that carries
     * one is found by the first of those without this being touched.
     */
    private static List<Written> identitiesIn(JsonNode node, List<Written> into) {
        if (node.isArray()) {
            node.forEach(child -> identitiesIn(child, into));
            return into;
        }
        if (!node.isObject()) {
            return into;
        }
        JsonNode sourceId = node.get("sourceId");
        if (sourceId != null && sourceId.isString()) {
            into.add(new Written("sourceId", sourceId.asString()));
        }
        JsonNode scope = node.get("scope");
        if (scope != null && "source".equals(scope.asString())) {
            into.add(new Written("subject", node.get("subject").asString()));
        }
        for (String name : node.propertyNames()) {
            // Not the table itself, whose keys are the identities and whose values are names. Reading
            // it back would let a document explain itself with its own entries.
            if (!name.equals("sources")) {
                identitiesIn(node.get(name), into);
            }
        }
        return into;
    }

    private record Streams(int code, String out, String err) {}

    private static Streams run(Map<String, String> byName, String... extraArgs) throws Exception {
        Path dir = Files.createTempDirectory("souther-explained-sources");
        List<String> args = new ArrayList<>(List.of("examples"));
        args.addAll(List.of(extraArgs));
        for (Map.Entry<String, String> source : byName.entrySet()) {
            Path file = dir.resolve(source.getKey());
            Files.createDirectories(file.getParent());
            Files.writeString(file, source.getValue());
            args.add(file.toString());
        }
        PrintStream originalOut = System.out;
        PrintStream originalErr = System.err;
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        System.setOut(new PrintStream(out, true, StandardCharsets.UTF_8));
        System.setErr(new PrintStream(err, true, StandardCharsets.UTF_8));
        int code;
        try {
            code = Main.dispatch(args.toArray(String[]::new));
        } finally {
            System.setOut(originalOut);
            System.setErr(originalErr);
        }
        assertFalse(out.toString(StandardCharsets.UTF_8).isBlank(),
                "the command wrote a report: " + err.toString(StandardCharsets.UTF_8));
        return new Streams(code, out.toString(StandardCharsets.UTF_8),
                err.toString(StandardCharsets.UTF_8));
    }
}
