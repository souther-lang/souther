package souther.compiler.apt;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A compile error found by the annotation processor reaches the build log as the same rendered
 * diagnostic the CLI prints — title, position, source line with a caret, message, and hint — not as
 * the exception's internal detail string.
 */
class SoutherProcessorDiagnosticTest {

    @Test
    void aTypeErrorIsRenderedWithItsSourceLine(@TempDir Path dir) throws IOException {
        Path source = write(dir, "member.sou", """
                module demo
                data Out = { v: Int }
                behavior f : (s: String) -> Out
                    constructs Out
                let f (s) = Out { v = s }
                """);

        String reported = compile(dir, source, "en");

        assertTrue(reported.contains("member.sou:5:"), reported);          // which file, where
        assertTrue(reported.contains("let f (s) = Out { v = s }"), reported);  // the offending line
        assertTrue(reported.contains("^"), reported);                      // the caret under it
        assertTrue(reported.contains("Int"), reported);                    // the found/expected block
    }

    @Test
    void theMessageIsRenderedInTheChosenLanguage(@TempDir Path dir) throws IOException {
        Path source = write(dir, "member.sou", """
                module demo
                data Out = { v: Int }
                behavior f : (s: String) -> Out
                    constructs Out
                let f (s) = Out { v = s }
                """);

        String ja = compile(dir, source, "ja");

        assertTrue(ja.contains("フィールド"), ja);
    }

    @Test
    void aMultiFileModuleSetNamesTheFileTheErrorIsIn(@TempDir Path dir) throws IOException {
        Path sources = Files.createDirectories(dir.resolve("souther"));
        write(sources, "a.sou", """
                module a exposing ( 従業員ID )
                data 従業員ID = String
                """);
        write(sources, "b.sou", """
                module b
                import a ( 従業員ID )
                data Out = { v: Int }
                behavior f : (who: 従業員ID) -> Out
                    constructs Out
                let f (who) = Out { v = who }
                """);

        String reported = compile(dir, sources, "en");

        assertTrue(reported.contains("b.sou:6:"), reported);
        assertTrue(reported.contains("let f (who) = Out { v = who }"), reported);
    }

    @Test
    void aSyntaxErrorIsRenderedTheSameWay(@TempDir Path dir) throws IOException {
        Path source = write(dir, "broken.sou", """
                module demo
                data Out = { v: Int
                """);

        String reported = compile(dir, source, "en");

        assertTrue(reported.contains("broken.sou:"), reported);
        assertTrue(reported.contains("^"), reported);
    }

    @Test
    void everyFailingExampleRowIsReportedWithItsOwnReason(@TempDir Path dir) throws IOException {
        Path source = write(dir, "member.sou", """
                module demo
                import String ( length )
                data 従業員ID = String
                    invariant length(value) > 0
                data 名札 = { id: 従業員ID }
                behavior 作る : (id: 従業員ID) -> 名札
                    constructs 名札
                let 作る (id) = 名札 { id = id }
                example 作る
                  | "first" : (従業員ID("")) -> 名札 { id = 従業員ID("x") }
                  | "second" : (従業員ID("")) -> 名札 { id = 従業員ID("y") }
                """);

        String reported = compile(dir, source, "en");

        assertTrue(reported.contains("member.sou:10:"), reported);   // the first failing row
        assertTrue(reported.contains("member.sou:11:"), reported);   // and the second
        assertFalse(reported.contains("examples do not hold"),
                "a count does not stand in for the reason: " + reported);
    }

    /** What the processor reported as an error. The compilation must fail: these are all errors. */
    private static String compile(Path dir, Path source, String lang) throws IOException {
        ProcessorRun run = ProcessorRun.of(dir, source, lang);
        assertFalse(run.ok(), "the compilation should have failed: " + run.errors());
        return run.errors();
    }

    private static Path write(Path dir, String name, String content) throws IOException {
        return ProcessorRun.write(dir, name, content);
    }
}
