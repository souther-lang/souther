package souther.cli;

import org.junit.jupiter.api.Test;

import souther.compiler.report.AdequacyReport;

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
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A document that names a source by an identity says what that identity was.
 *
 * <p>The identity is what the report carries, and rightly: it is what the compilation refers to the
 * source by, and so what makes two reasons about one file the same reason, where a name is chosen
 * from the files in front of one reader and is no key. What follows is
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

    /**
     * A model whose rows are never evaluated: a composition names a stage that does not exist, so
     * the module has no meaning to emit and nothing of it runs. Its report carries a reason about
     * the row that went unread, and a row is named by the source it is written in — which is the
     * identity this test is here to read.
     *
     * <p>A name and not a body, because that is what leaves the whole source unobserved. A body
     * that does not check leaves the bodies that do check runnable and their rows observed.
     */
    private static String stopped(String module, String type) {
        return String.format("""
                module %s

                data %s = Int
                    invariant value >= 0

                behavior passThrough : (a: %s) -> %s
                let passThrough (a) = a

                behavior onwards = passThrough >-> nosuch

                example passThrough
                    | (%s(1)) -> %s(1)
                """, module, type, type, type, type, type);
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

    /** A model that leaves nothing to say about a source: nobody wrote a row in it, so there is no
     * row for its account to name, and its body has no arms for an unreached one to be reported
     * at. */
    private static final String NOTHING_TO_SAY = """
            module example.plain

            data Ok = { n: Int }

            behavior keep : (v: Int) -> Ok
                constructs Ok

            let keep (v) = Ok { n = v }
            """;

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /**
     * Every identity the document writes is one the document explains.
     *
     * <p>Every field this can read is in this run on purpose: a position pointing at an arm nothing
     * reached, a position under a reason about a row nothing was observed for, and the source a row
     * subject is named by — under the verdict this document holds open and under the obligation the
     * row answers. They are written by different code and were explained by none of it.
     *
     * <p>The one spelling not here is a reason whose {@code subject} is itself a source identity,
     * which is not reachable from a command: it is written for a source whose contents nothing could
     * read, and what a document does with one is asked where such a fact can be built.
     */
    @Test
    void everySourceIdentityWrittenHasAnEntry() throws Exception {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put("arms.sou", ONE_ARM_UNREACHED);
        sources.put("stopped.sou", stopped("example.stopped", "Qty"));

        JsonNode report = JSON.readTree(run(sources, "--format", "json").out());

        List<Written> written = identitiesIn(report, new ArrayList<>());
        // Every field the vocabulary holds, so that what this walks is what a reader of the schema
        // would walk. A run reaching one of them and not the others would pass this over the field
        // it reached and say nothing about the rest.
        assertEquals(IDENTITY_FIELDS,
                written.stream().map(Written::field).collect(Collectors.toCollection(
                        LinkedHashSet::new)),
                () -> "the identities this document writes are " + written + " in " + report);

        Set<String> explained = new LinkedHashSet<>(report.get("sources").propertyNames());
        for (Written each : written) {
            assertTrue(explained.contains(each.sourceId()),
                    each + " is written and not explained by " + explained);
        }
    }

    /**
     * And every entry of the table is a source the document names.
     *
     * <p>The other direction, asked of the document and not of a fixture. What it rules out is a
     * table that explains more than the document carries — a consumer reading it as the report's
     * subject would be reading in files nothing here says anything about.
     *
     * <p><b>Why not asked by compiling a source nothing mentions.</b> That is what the test below
     * does, and it is a statement about the command rather than about the document: it holds while
     * such a source can be built, and a document that grows a new place to name one takes the case
     * away without taking the claim away. The row account did exactly that — a behavior with a row
     * now names the source that row is written in — and the test below went on passing about a
     * narrower thing. This asks the document, where the two ends are both in hand whatever a
     * fixture happens to reach.
     */
    @Test
    void andEveryEntryOfTheTableIsASourceTheDocumentNames() throws Exception {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put("arms.sou", ONE_ARM_UNREACHED);
        sources.put("stopped.sou", stopped("example.stopped", "Qty"));

        JsonNode report = JSON.readTree(run(sources, "--format", "json").out());

        Set<String> named = new LinkedHashSet<>();
        for (Written each : identitiesIn(report, new ArrayList<>())) {
            named.add(each.sourceId());
        }
        List<String> explained = List.copyOf(report.get("sources").propertyNames());
        assertFalse(explained.isEmpty(), "this document explains a source: " + report);
        for (String each : explained) {
            assertTrue(named.contains(each),
                    each + " is explained and named by no identity in " + report);
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
            assertTrue(asText.out().contains("`passThrough #1 in " + name + "`"),
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

    /**
     * A field named for a source is defined as one, so the name and the definition agree.
     *
     * <p>The vocabulary above is the set of fields written with the shared definition, and a field
     * that carries an identity while spelling it out for itself is outside that set — which is how
     * the identity a row subject carries came to be written by the document and read by nothing.
     * Asked of the names because that is the half a reader of the document sees: two fields called
     * the same thing that are not the same thing is the other way this drifts.
     */
    @Test
    void everyFieldNamedForASourceIsDefinedAsOne() {
        List<Defined> named = new ArrayList<>();
        propertiesNamedForASource(schema(), named);

        assertFalse(named.isEmpty(), "this schema has fields named for a source");
        for (Defined each : named) {
            JsonNode ref = each.definition().get("$ref");
            assertTrue(ref != null && SOURCE_IDENTITY.equals(ref.asString()),
                    () -> "`" + each.name() + "` is named for a source and is written out as "
                            + each.definition() + ", so nothing reading the definition finds it");
        }
    }

    /** One place the schema defines a field, and what it defines it as. */
    private record Defined(String name, JsonNode definition) {}

    /** Every property of the schema whose name says it is a source, wherever it sits. */
    private static void propertiesNamedForASource(JsonNode node, List<Defined> into) {
        if (node.isArray()) {
            node.forEach(child -> propertiesNamedForASource(child, into));
            return;
        }
        if (!node.isObject()) {
            return;
        }
        JsonNode properties = node.get("properties");
        if (properties != null) {
            for (String property : properties.propertyNames()) {
                if (property.equals("source") || property.equals("sourceId")) {
                    into.add(new Defined(property, properties.get(property)));
                }
            }
        }
        for (String name : node.propertyNames()) {
            propertiesNamedForASource(node.get(name), into);
        }
    }

    /** Where a source identity was written, and which one. */
    private record Written(String field, String sourceId) {}

    /**
     * The fields the schema defines as a source identity, which is what one is written under.
     *
     * <p>Read from the schema and not listed here, so that the document and what reads it take the
     * set from one place. A field carrying an identity and defined inline instead would be invisible
     * to this, which is what {@link #everyFieldNamedForASourceIsDefinedAsOne} refuses.
     */
    private static final Set<String> IDENTITY_FIELDS = identityFieldsOf(schema());

    private static Set<String> identityFieldsOf(JsonNode schema) {
        Set<String> out = new LinkedHashSet<>();
        definedAsAnIdentity(schema, null, out);
        return out;
    }

    /** Every property of {@code node} — at any depth — written as the shared definition. */
    private static void definedAsAnIdentity(JsonNode node, String named, Set<String> into) {
        if (node.isArray()) {
            node.forEach(child -> definedAsAnIdentity(child, null, into));
            return;
        }
        if (!node.isObject()) {
            return;
        }
        JsonNode ref = node.get("$ref");
        if (named != null && ref != null && SOURCE_IDENTITY.equals(ref.asString())) {
            into.add(named);
        }
        JsonNode properties = node.get("properties");
        if (properties != null) {
            for (String property : properties.propertyNames()) {
                definedAsAnIdentity(properties.get(property), property, into);
            }
        }
        for (String name : node.propertyNames()) {
            if (!name.equals("properties")) {
                definedAsAnIdentity(node.get(name), null, into);
            }
        }
    }

    private static final String SOURCE_IDENTITY = "#/$defs/sourceIdentity";

    /** The schema shipped beside this compiler, which is what a reader validates against. */
    private static JsonNode schema() {
        try (java.io.InputStream in = AdequacyReport.class.getResourceAsStream(
                "/souther/adequacy-schema-" + AdequacyReport.SCHEMA_VERSION + ".json")) {
            return JSON.readTree(in);
        } catch (java.io.IOException cannotRead) {
            throw new IllegalStateException("the schema is shipped beside this", cannotRead);
        }
    }

    /**
     * The source identities anywhere in a document.
     *
     * <p>Which fields carry one is asked of the schema rather than written here. A field that
     * carries an identity says so by being defined as {@code sourceIdentity}, so this walks the
     * schema for the names of those fields and then reads them wherever they sit. A field added to
     * the document is covered by the definition it is written with, which is the one place the fact
     * is stated — kept here as a list, it was a list of the places an identity was emitted the day
     * it was written, and the next place to emit one was outside it.
     *
     * <p>The one spelling that cannot say so is a reason's {@code subject}, which is an identity
     * exactly where its {@code scope} is {@code source} and is the name an author wrote everywhere
     * else. That much is read from the pair, and the schema's own account of the table says so.
     */
    private static List<Written> identitiesIn(JsonNode node, List<Written> into) {
        if (node.isArray()) {
            node.forEach(child -> identitiesIn(child, into));
            return into;
        }
        if (!node.isObject()) {
            return into;
        }
        for (String field : IDENTITY_FIELDS) {
            JsonNode written = node.get(field);
            if (written != null && written.isString()) {
                into.add(new Written(field, written.asString()));
            }
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
