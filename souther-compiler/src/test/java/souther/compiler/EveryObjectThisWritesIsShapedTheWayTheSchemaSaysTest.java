package souther.compiler;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;
import souther.compiler.diag.SourceNameResolver;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.io.IOException;
import java.io.InputStream;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every object this writes has the keys the shipped schema declares for it, and all of them.
 *
 * <p>The schema and the writer are two accounts of one document, and nothing made them agree except
 * somebody remembering to change both. What held them together was a check naming the objects it
 * looked at — {@code findings} and {@code partition.unanswered}, the two a single earlier defect
 * happened to touch. An object nobody had named was a place the two could disagree in silence, and
 * they did: issue #953 added {@code status} and {@code weakening} to ten objects and made four
 * fields conditional, and every document this compiler wrote was refused by the schema shipped
 * beside it for a year's worth of readers before anybody looked.
 *
 * <p><b>So this names nothing.</b> It walks the document and the schema together, from the root, and
 * reaches whatever the two of them reach. A key moved to another object is caught wherever it lands,
 * and an object added later is checked without being told about.
 *
 * <p><b>It is not a validator, and it refuses to look like one.</b> What it understands is the set
 * of keywords listed in {@link #UNDERSTOOD}; meeting any other is a failure rather than something
 * skipped, because a walk that steps over what it does not know is a check that stops saying
 * anything the moment the schema grows — which is how the check it replaces came to pass over a
 * document with twenty-seven violations in it.
 */
class EveryObjectThisWritesIsShapedTheWayTheSchemaSaysTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /**
     * The keywords this knows what to do with.
     *
     * <p>Two kinds. Some decide which keys an object may have and must have, and are what this is
     * about; the rest constrain a value and are none of its business — but they are listed all the
     * same, so that a keyword the schema gains is a decision somebody makes here rather than a
     * silence.
     */
    private static final Set<String> UNDERSTOOD = Set.of(
            // the shape of an object, which is the whole of what this checks
            "properties", "required", "additionalProperties", "items", "$ref",
            // compositions: their branches are read for the keys they allow, never for what they
            // require, since which branch a value took is not this walk's question
            "oneOf", "anyOf", "allOf", "if", "then", "else", "not", "dependentRequired",
            // constraints on a value, which say nothing about keys
            "type", "enum", "const", "minimum", "pattern", "minItems", "maxItems",
            "uniqueItems", "contains", "minContains", "maxContains",
            // prose and plumbing
            "description", "title", "$schema", "$id", "$defs");

    /** A model whose report reaches a measure of every kind, made in full, in part, and not at all. */
    private static final String MODEL = """
            module m

            data R = { a: Int }
            data Found
            data Missing

            behavior f : (r: R) -> Found | Missing
                ensures Found -> r.a <= Int.min(20, 30)
                ensures Found -> r.a >= Int.min(40, 50)
            let f (r) = if r.a >= 30 * 2 then Found else Missing

            behavior unwritten : (r: R) -> Found | Missing

            behavior named : (r: R) -> Found | Missing
            let named (r) = if r.a == 7 then Found else Missing

            example f
                | "one" : (R { a = 1 }) -> Missing

            example named
                | "seven" : (R { a = 7 }) -> Found
            """;

    @Test
    void aDocumentThisWritesIsShapedTheWayTheSchemaSays() {
        Walk walk = new Walk(schema());
        walk.of(document(), "");
        assertTrue(walk.objects > 20,
                () -> "the model reaches the objects of the document: " + walk.objects);
        assertEquals(List.of(), walk.wrong, "what the schema shipped beside this refuses");
    }

    /**
     * A point owing no row is closed, rather than listing what it may not have.
     *
     * <p>The list was the keys of the owed side written a second time, with nothing holding the two
     * in step, and it fell behind twice: `weakening` was never added to it, and `writableBecause`
     * was added to the schema and not to it, so the schema took a document naming grounds for a
     * point nobody is owed a row at. Closed, there is no list to fall behind — a key added to the
     * item is forbidden here by not having been named.
     *
     * <p>Which is what this holds: not that some set of keys is forbidden, but that the branch is
     * still the kind of thing that forbids by default. Written the other way round, the check would
     * be the list a second time.
     */
    @Test
    void aPointOwingNoRowIsClosedAndNotAListOfWhatItMayNotHave() {
        JsonNode item = schema().get("$defs").get("partition").get("properties").get("boundaries")
                .get("items").get("properties").get("items").get("items");
        JsonNode notOwed = null;
        for (JsonNode branch : item.get("oneOf")) {
            if (branch.has("required") && branch.get("required").get(0).asString().equals("notOwed")) {
                notOwed = branch;
            }
        }
        assertNotNull(notOwed, "the item has a branch for a point owing no row");
        assertTrue(notOwed.has("additionalProperties")
                        && !notOwed.get("additionalProperties").asBoolean(),
                "the branch forbids what it does not name, rather than naming what it forbids");
        Set<String> named = new java.util.LinkedHashSet<>();
        notOwed.get("properties").propertyNames().forEach(named::add);
        assertEquals(Set.of("point", "location", "notOwed"), named,
                "and what it names is which point of the border it is, where on the quantity it is,"
                        + " and why no row is owed there");
    }

    /**
     * A document written before a key was added is still a document of this version.
     *
     * <p>Held on the key added last, which is {@code writableBecause}. The preamble says a key added
     * since does not raise the version, and what that promises is this: the same schema takes a
     * document with the key and a document without it. So an absent array is a producer that predates
     * the field and never a point with no grounds — that is written as an empty array, and a reader
     * that took the two for one answer would read every older document as a corpus nothing shows
     * anything about.
     */
    @Test
    void aDocumentWrittenBeforeAKeyWasAddedIsStillOfThisVersion() {
        JsonNode without = document();
        int taken = strip(without, "writableBecause");
        assertTrue(taken > 0, "the document carries the key, or this strips nothing");

        Walk walk = new Walk(schema());
        walk.of(without, "");
        assertEquals(List.of(), walk.wrong,
                "the shipped schema refuses a document written before the key existed");
    }

    /** Every occurrence of {@code key} taken out, and how many there were. */
    private static int strip(JsonNode node, String key) {
        int taken = 0;
        if (node instanceof tools.jackson.databind.node.ObjectNode object) {
            if (object.has(key)) {
                object.remove(key);
                taken++;
            }
            List<String> names = new ArrayList<>();
            object.propertyNames().forEach(names::add);
            for (String name : names) {
                taken += strip(object.get(name), key);
            }
        } else if (node.isArray()) {
            for (JsonNode each : node) {
                taken += strip(each, key);
            }
        }
        return taken;
    }

    /**
     * And so is every document checked in as an answer.
     *
     * <p>Those are what a reader of this project meets first, and they are rewritten by a flag
     * rather than by hand — so a change that moved the shape moved them with it, and nothing on the
     * way said the shape had stopped matching what ships beside them.
     */
    @Test
    void soIsEveryAnswerCheckedIn() throws IOException {
        Path corpus = Path.of("src/test/resources/souther/compiler/conformance");
        assertTrue(Files.isDirectory(corpus), () -> "the corpus is at " + corpus.toAbsolutePath());
        List<Path> answers;
        try (Stream<Path> files = Files.walk(corpus)) {
            answers = files.filter(each -> each.getFileName().toString().endsWith(".report.json"))
                    .sorted().toList();
        }
        assertTrue(!answers.isEmpty(), "there is an answer checked in");

        JsonNode schema = schema();
        List<String> wrong = new ArrayList<>();
        for (Path each : answers) {
            Walk walk = new Walk(schema);
            walk.of(JSON.readTree(read(each)), each.getFileName().toString());
            wrong.addAll(walk.wrong);
        }
        assertEquals(List.of(), wrong, "an answer the schema shipped beside it refuses");
    }

    /** The document and the schema, walked together. */
    private static final class Walk {

        private final JsonNode schema;
        private final List<String> wrong = new ArrayList<>();
        private int objects;

        Walk(JsonNode schema) {
            this.schema = schema;
        }

        void of(JsonNode node, String at) {
            of(node, schema, at);
        }

        private void of(JsonNode node, JsonNode declared, String at) {
            JsonNode said = resolved(declared);
            understand(said, at);
            if (node.isObject()) {
                objects++;
                Set<String> may = declaredIn(said);
                if (closed(said)) {
                    node.propertyNames().forEach(key -> {
                        if (!may.contains(key)) {
                            wrong.add(at + ": the schema declares no `" + key + "` here");
                        }
                    });
                }
                // Only what the object itself requires. Which branch of a composition a value took
                // is a question about the value, and answering it here would report a document as
                // short of a key another branch asks for.
                if (said.has("required")) {
                    said.get("required").forEach(key -> {
                        if (!node.has(key.asString())) {
                            wrong.add(at + ": the schema requires a `" + key.asString() + "` here");
                        }
                    });
                }
                node.properties().forEach(entry -> {
                    JsonNode under = declares(said, entry.getKey());
                    if (under != null) {
                        of(entry.getValue(), under, at + "/" + entry.getKey());
                    }
                });
            } else if (node.isArray()) {
                JsonNode items = itemsOf(said);
                if (items != null) {
                    for (int i = 0; i < node.size(); i++) {
                        of(node.get(i), items, at + "[" + i + "]");
                    }
                }
            }
        }

        /** Every keyword of this schema object, held to what this walk was taught. */
        private void understand(JsonNode said, String at) {
            said.propertyNames().forEach(keyword -> {
                if (!UNDERSTOOD.contains(keyword)) {
                    wrong.add(at + ": `" + keyword + "` is a keyword this walk was never taught,"
                            + " and stepping over one is how a check stops saying anything");
                }
            });
        }

        private JsonNode resolved(JsonNode said) {
            JsonNode at = said;
            while (at.has("$ref")) {
                String name = at.get("$ref").asString();
                at = schema.get("$defs").get(name.substring(name.lastIndexOf('/') + 1));
                assertNotNull(at, () -> "the schema refers to " + name + " and does not define it");
            }
            return at;
        }

        /** Whether an undeclared key is a refusal here, which is what makes this worth asking. */
        private boolean closed(JsonNode said) {
            JsonNode more = said.get("additionalProperties");
            return more != null && more.isBoolean() && !more.booleanValue();
        }

        /** Every key this object may have, over the object itself and every branch beside it. */
        private Set<String> declaredIn(JsonNode said) {
            Set<String> out = new LinkedHashSet<>();
            if (said.has("properties")) {
                said.get("properties").propertyNames().forEach(out::add);
            }
            for (String branch : List.of("oneOf", "anyOf", "allOf")) {
                if (said.has(branch)) {
                    said.get(branch).forEach(each -> out.addAll(declaredIn(resolved(each))));
                }
            }
            for (String arm : List.of("if", "then", "else", "not")) {
                if (said.has(arm)) {
                    out.addAll(declaredIn(resolved(said.get(arm))));
                }
            }
            return out;
        }

        /** Where the schema says what is under one key, or null where it says nothing. */
        private JsonNode declares(JsonNode said, String key) {
            if (said.has("properties") && said.get("properties").has(key)) {
                return said.get("properties").get(key);
            }
            for (String branch : List.of("oneOf", "anyOf", "allOf")) {
                if (said.has(branch)) {
                    for (JsonNode each : said.get(branch)) {
                        JsonNode under = declares(resolved(each), key);
                        if (under != null) {
                            return under;
                        }
                    }
                }
            }
            for (String arm : List.of("then", "else")) {
                if (said.has(arm)) {
                    JsonNode under = declares(resolved(said.get(arm)), key);
                    if (under != null) {
                        return under;
                    }
                }
            }
            return null;
        }

        private JsonNode itemsOf(JsonNode said) {
            return said.has("items") ? said.get("items") : null;
        }
    }

    private static JsonNode schema() {
        try (InputStream in =
                     AdequacyReport.class.getResourceAsStream(AdequacyReport.SCHEMA_RESOURCE)) {
            assertNotNull(in, AdequacyReport.SCHEMA_RESOURCE + " ships beside the compiler");
            return JSON.readTree(new String(in.readAllBytes(), StandardCharsets.UTF_8));
        } catch (IOException cannotRead) {
            throw new UncheckedIOException(cannotRead);
        }
    }

    private static String read(Path at) {
        try {
            return Files.readString(at, StandardCharsets.UTF_8);
        } catch (IOException cannotRead) {
            throw new UncheckedIOException(cannotRead);
        }
    }

    private static JsonNode document() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return JSON.readTree(AdequacyReport.of(compilation).json(SourceNameResolver.identity()));
    }
}
