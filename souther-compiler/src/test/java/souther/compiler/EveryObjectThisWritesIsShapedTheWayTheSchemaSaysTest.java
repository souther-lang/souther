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
            "contains", "minContains", "maxContains",
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

            example f
                | "one" : (R { a = 1 }) -> Missing
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
                     AdequacyReport.class.getResourceAsStream("/souther/adequacy-schema-6.json")) {
            assertNotNull(in, "adequacy-schema-6.json ships beside the compiler");
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
