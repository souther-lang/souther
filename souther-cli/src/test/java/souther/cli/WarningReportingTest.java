package souther.cli;

import souther.compiler.source.SourceId;

import souther.compiler.diag.Located;
import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A warning reaches the command line the way an error does: the same header, the offending line and
 * a caret under it, in the language and the format the flags asked for. A warning is the whole of
 * what the invariant checker has to say about a construction it cannot prove, so one printed without
 * its position cannot be attributed to the construction it is about.
 */
class WarningReportingTest {

    /** One unproven construction, on line 8. */
    private static final String UNPROVEN = """
            data Eaches = Int
                invariant value >= 0

            behavior wrap : (n: Int) -> Eaches
                constructs Eaches
            let wrap (n) = {
                let m = n
                Eaches(m)
            }
            """;

    @Test
    void aWarningIsPrintedWithItsPositionAndSourceLine() throws Exception {
        Path file = write("probe.sou", UNPROVEN);

        String reported = compile(file, "--lang", "en");

        assertTrue(reported.contains("probe.sou:8:5"), reported);      // which file, where in it
        assertTrue(reported.contains("Eaches(m)"), reported);          // the offending line
        assertTrue(reported.contains("^"), reported);                  // the caret under it
        assertTrue(reported.contains("E2011"), reported);
    }

    @Test
    void theHeaderSaysItIsAWarning() throws Exception {
        Path file = write("probe.sou", UNPROVEN);

        String reported = compile(file, "--lang", "en");

        assertTrue(reported.contains("INVARIANT (WARNING)"),
                "a warning that is titled by what it is about still says which severity it is: "
                        + reported);
        assertFalse(reported.contains("ERROR"), reported);
    }

    @Test
    void theWarningFollowsTheChosenLanguage() throws Exception {
        Path file = write("probe.sou", UNPROVEN);

        String ja = compile(file, "--lang", "ja");

        assertTrue(ja.contains("(警告)"), ja);
        assertTrue(ja.contains("不変条件に違反する可能性があります"), ja);
    }

    @Test
    void jsonRendersTheWarningAsOneObjectWithItsRegion() throws Exception {
        Path file = write("probe.sou", UNPROVEN);

        String reported = compile(file, "--format", "json", "--lang", "en").strip();

        assertFalse(reported.contains("\n"), "one diagnostic is one line, not an array: " + reported);
        assertTrue(reported.startsWith("{") && reported.endsWith("}"), reported);
        assertTrue(reported.contains("\"severity\":\"warning\""), reported);
        assertTrue(reported.contains("\"code\":\"E2011\""), reported);
        assertTrue(reported.contains("\"file\":\"probe.sou\""), reported);
        assertTrue(reported.contains("\"startLine\":8"), reported);
    }

    /**
     * A compile of one file names that file, as a compile of several does, and the line is quoted
     * from it.
     *
     * <p>It used to name none, on the grounds that the caller knows the file it handed over. What
     * the renderer then had to do was fall back to the one file it was given — and a secondary in
     * that same file, which named it, read as being somewhere else.
     */
    @Test
    void aSingleFileWarningNamesTheOneSourceAndIsQuotedFromIt() throws Exception {
        Path file = write("probe.sou", UNPROVEN);
        List<Located> warnings = new ArrayList<>();

        Main.compileToDir(List.of(file), Files.createTempDirectory("souther-warn-out"),
                List.of(), warnings);

        assertEquals(1, warnings.size(), warnings.toString());
        assertEquals(new SourceId("0"), warnings.get(0).primarySourceId(),
                "the one source is a source, and a warning in it says so");
        assertTrue(compile(file, "--lang", "en").contains("probe.sou:8:5"));
    }

    @Test
    void aWarningNamesTheFileOfTheModuleItIsIn() throws Exception {
        Path dir = Files.createTempDirectory("souther-warn");
        Path a = dir.resolve("a.sou");
        Path b = dir.resolve("b.sou");
        Files.writeString(a, """
                module a exposing ( Eaches, wrap )

                data Eaches = Int
                    invariant value >= 0

                behavior wrap : (n: Int) -> Eaches
                    constructs Eaches
                let wrap (n) = {
                    let m = n
                    Eaches(m)
                }
                """);
        Files.writeString(b, """
                module b

                import a ( Eaches )

                data Box = { it: Eaches }
                """);

        String reported = capture(() -> Main.main(new String[]{
                "compile", "--lang", "en", a.toString(), b.toString(),
                "-d", Files.createTempDirectory("souther-warn-out").toString()})).err();

        assertTrue(reported.contains("a.sou:10:5"),
                "the warning belongs to the module that declares the construction: " + reported);
        assertFalse(reported.contains("b.sou"), reported);
    }

    @Test
    void runWarnsOnStderrAndKeepsItsResultOnStdout() throws Exception {
        Path file = write("probe.sou", UNPROVEN);

        Captured ran = capture(() -> Main.main(
                new String[]{"run", "--lang", "en", file.toString(), "--input", "5"}));

        assertEquals("5", ran.out().strip(),
                "a caller piping the result reads the behavior's output and nothing else");
        assertTrue(ran.err().contains("probe.sou:8:5"), ran.err());
    }

    /**
     * The run that aborts is the one the warning predicted, so it is the last one that should
     * swallow it. The compile finishes before the run begins, so the warnings are already the whole
     * set by the time the abort is raised, and {@code Main} renders them from its catch.
     *
     * <p>Driven through {@link Runner} rather than {@link Main#main}, because the failing path ends
     * in {@code System.exit} and would take the test JVM with it.
     */
    @Test
    void theWarningsSurviveARunThatAborts() throws Exception {
        Path file = write("probe.sou", UNPROVEN);
        List<Located> warnings = new ArrayList<>();

        assertThrows(Runner.RunException.class, () -> Runner.runCli(
                new String[]{file.toString(), "--input", "-1"}, warnings));

        assertEquals(1, warnings.size(), warnings.toString());
        assertEquals("E2011", warnings.get(0).diagnostic().code());
    }

    @Test
    void runKeepsTheStreamsApartInJsonToo() throws Exception {
        Path file = write("probe.sou", UNPROVEN);

        Captured ran = capture(() -> Main.main(new String[]{
                "run", "--format", "json", "--lang", "en", file.toString(), "--input", "5"}));

        assertEquals("5", ran.out().strip());
        assertTrue(ran.err().contains("\"severity\":\"warning\""), ran.err());
    }

    /** What {@code souther compile} writes to stderr for {@code file}. */
    private static String compile(Path file, String... flags) throws Exception {
        List<String> args = new ArrayList<>(List.of("compile"));
        args.addAll(List.of(flags));
        args.add(file.toString());
        args.add("-d");
        args.add(Files.createTempDirectory("souther-warn-out").toString());
        return capture(() -> Main.main(args.toArray(new String[0]))).err();
    }

    /** What an action wrote to each stream. Both are captured because the point of several of these
     *  tests is that the two carry different things. */
    private record Captured(String out, String err) {}

    private static Captured capture(Action action) throws Exception {
        PrintStream outWas = System.out;
        PrintStream errWas = System.err;
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        System.setOut(new PrintStream(out, true, StandardCharsets.UTF_8));
        System.setErr(new PrintStream(err, true, StandardCharsets.UTF_8));
        try {
            action.run();
        } finally {
            System.setOut(outWas);
            System.setErr(errWas);
        }
        return new Captured(out.toString(StandardCharsets.UTF_8),
                err.toString(StandardCharsets.UTF_8));
    }

    private static Path write(String name, String content) throws Exception {
        Path file = Files.createTempDirectory("souther-warn").resolve(name);
        Files.writeString(file, content);
        return file;
    }

    private interface Action {
        void run() throws Exception;
    }
}
