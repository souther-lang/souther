package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceNameResolver;
import souther.compiler.query.Compilation;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a source is called is the caller's answer, and a report asks it rather than printing the id.
 *
 * <p>A compile identifies its sources by whatever the caller handed them over as: a position in a
 * list for a build, a document URI for an editor. A reason about a source carries that id, which is
 * the right thing for it to carry — two reasons are the same reason when they are about the same
 * source, and only an identity settles that. What a person is shown is a different question, and its
 * answer is not a property of the source: what to call {@code a/model.sou} depends on whether some
 * other file in the same compile is also called {@code model.sou}.
 *
 * <p>So the id stays in the report and the name is given at the point it is rendered. These hold
 * both halves: that a person is shown a file name, and that the identity a build reads is still an
 * id.
 */
class AReportNamesASourceTheWayItsCallerDoesTest {

    /** A model whose rows are never evaluated: the `constructs` clause promises a construction the
     * body does not make, which is raised before anything runs. */
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

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /**
     * One file, named.
     *
     * <p>A compile of one source tells its caller no source id at all, on the reasoning that the
     * caller knows the file it handed over. The report does not go through that and reads the ids
     * the compilation holds, so the run that names no source named one anyway — as `0`.
     */
    @Test
    void aSingleSourceIsNamedAndNotNumbered() throws Exception {
        Streams ran = run(Map.of("zeroname.sou", stopped("example.zeroname", "Amount")));

        assertTrue(ran.out().contains("no rows were read from `zeroname.sou`"), ran.out());
        assertFalse(ran.out().contains("`0`"), "an id is not a name: " + ran.out());
    }

    /** Several files, each named the way the diagnostics above them name it. */
    @Test
    void eachOfSeveralSourcesIsNamed() throws Exception {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put("other.sou", stopped("example.other", "Qty"));
        sources.put("zeroname.sou", stopped("example.zeroname", "Amount"));

        Streams ran = run(sources);

        assertTrue(blockOf(ran.out(), "example.other")
                        .contains("no rows were read from `other.sou`"), ran.out());
        assertTrue(blockOf(ran.out(), "example.zeroname")
                        .contains("no rows were read from `zeroname.sou`"), ran.out());
    }

    /**
     * And the name is the one the whole compile agrees on, not the basename.
     *
     * <p>Two modules may each keep a {@code model.sou}, and a reader told that the rows of
     * {@code model.sou} were not read has learned nothing. The rule for what to call a file is
     * already written for diagnostics and is the same rule here — which is why the name cannot be a
     * property of the source: it is a fact about the set of files in front of the reader.
     */
    @Test
    void aNameSharedWithAnotherFileIsSaidWithEnoughOfItsPath() throws Exception {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put("a/model.sou", stopped("example.a", "Qty"));
        sources.put("b/model.sou", stopped("example.b", "Amount"));

        Streams ran = run(sources);

        assertTrue(blockOf(ran.out(), "example.a")
                        .contains("no rows were read from `a/model.sou`"), ran.out());
        assertTrue(blockOf(ran.out(), "example.b")
                        .contains("no rows were read from `b/model.sou`"), ran.out());
    }

    /** The rows written beside the report read the same way, being read in the same terminal. */
    @Test
    void theGeneratedNoteNamesTheSourceToo() throws Exception {
        Streams ran = run(Map.of("zeroname.sou", stopped("example.zeroname", "Amount")),
                "--generate");

        assertTrue(ran.out().contains(
                        "// generation stopped for `passThrough`: no rows were read from"
                                + " `zeroname.sou`"), ran.out());
    }

    /**
     * What a build reads is still the identity.
     *
     * <p>A name is the shortest thing that tells this reader's files apart, so it is neither stable
     * across runs nor a key. Turning the JSON's subject into one would move the defect rather than
     * fix it: the document would then say what a person should be shown and no longer say which
     * source it is about.
     */
    @Test
    void theJsonSubjectIsStillTheSourceId() throws Exception {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put("other.sou", stopped("example.other", "Qty"));
        sources.put("zeroname.sou", stopped("example.zeroname", "Amount"));

        Streams ran = run(sources, "--format", "json");

        JsonNode modules = JSON.readTree(ran.out()).get("modules");
        Map<String, String> subjects = new LinkedHashMap<>();
        for (JsonNode module : modules) {
            for (JsonNode gap : module.get("incompleteness")) {
                if ("source".equals(gap.get("scope").asString())) {
                    subjects.put(module.get("module").asString(), gap.get("subject").asString());
                }
            }
        }
        assertEquals(Map.of("example.other", "0", "example.zeroname", "1"), subjects, ran.out());
    }

    /**
     * An id this command did not hand out is left as it is, and not read as the only file there is.
     *
     * <p>Two lookups run over the same list of files and answer differently, because they are asked
     * different questions. A diagnostic may name no source at all — a compile of one file tags its
     * problems with nothing, and the file handed over is the answer however the diagnostic is tagged
     * — so that lookup takes the single source whatever the id reads. A reason in a report always
     * names one, so an id that is none of these files is about a source this command did not hand
     * over, and answering with the only file would invent the correspondence this whole change is
     * about not guessing at.
     */
    @Test
    void anIdThisCommandDidNotHandOverIsNotResolvedToItsOnlyFile() {
        SourceNameResolver names = Main.namesOf(List.of(Path.of("a", "zeroname.sou")));

        assertEquals("zeroname.sou", names.nameOf(Compilation.idOfSourceIndex(0)));
        assertEquals("elsewhere.sou", names.nameOf("elsewhere.sou"),
                "an id from another caller stands for itself");
        assertEquals("1", names.nameOf("1"), "and so does a position this run has no file at");
    }

    /** The lines of the module's own section, which is where a reason about its sources is printed. */
    private static String blockOf(String out, String module) {
        StringBuilder block = new StringBuilder();
        boolean inside = false;
        for (String line : out.lines().toList()) {
            if (!line.startsWith(" ") && !line.isBlank()) {
                inside = line.startsWith(module + " ");
            }
            if (inside) {
                block.append(line).append('\n');
            }
        }
        return block.toString();
    }

    private record Streams(int code, String out, String err) {}

    private static Streams run(Map<String, String> byName, String... extraArgs) throws Exception {
        Path dir = Files.createTempDirectory("souther-named-sources");
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
        return new Streams(code, out.toString(StandardCharsets.UTF_8),
                err.toString(StandardCharsets.UTF_8));
    }
}
