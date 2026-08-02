package souther.compiler.apt;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A warning the invariant checker finds reaches the build log the way an error does. The build is
 * what a project is actually verified by, so a warning it does not carry lets unproven constructions
 * accumulate while everything stays green.
 *
 * <p>javac's {@code Messager} positions a message by {@code Element}, and the construction is inside
 * a {@code .sou} file javac has no element for, so the rendered snippet is what carries the position
 * across — as it already does for an error.
 */
class SoutherProcessorWarningTest {

    /** One unproven construction, on line 9. */
    private static final String UNPROVEN = """
            module demo

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
    void anUnprovenConstructionIsReportedAsAWarningWithItsPosition(@TempDir Path dir)
            throws IOException {
        Path source = ProcessorRun.write(dir, "probe.sou", UNPROVEN);

        ProcessorRun reported = ProcessorRun.of(dir, source, "en");

        assertTrue(reported.ok(), "a warning does not fail the build: " + reported.errors());
        assertTrue(reported.warnings().contains("probe.sou:10:5"), reported.warnings());
        assertTrue(reported.warnings().contains("Eaches(m)"), reported.warnings());
        assertTrue(reported.warnings().contains("^"), reported.warnings());
        assertTrue(reported.warnings().contains("E2011"), reported.warnings());
        assertTrue(reported.warnings().contains("INVARIANT (WARNING)"), reported.warnings());
    }

    @Test
    void theWarningFollowsTheChosenLanguage(@TempDir Path dir) throws IOException {
        Path source = ProcessorRun.write(dir, "probe.sou", UNPROVEN);

        ProcessorRun reported = ProcessorRun.of(dir, source, "ja");

        assertTrue(reported.warnings().contains("(警告)"), reported.warnings());
        assertTrue(reported.warnings().contains("不変条件に違反する可能性があります"),
                reported.warnings());
    }

    @Test
    void aWarningInAModuleSetNamesTheFileItIsIn(@TempDir Path dir) throws IOException {
        Path sources = Files.createDirectories(dir.resolve("souther"));
        ProcessorRun.write(sources, "a.sou", """
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
        ProcessorRun.write(sources, "b.sou", """
                module b

                import a ( Eaches )

                data Box = { it: Eaches }
                """);

        ProcessorRun reported = ProcessorRun.of(dir, sources, "en");

        assertTrue(reported.ok(), reported.errors());
        assertTrue(reported.warnings().contains("a.sou:10:5"), reported.warnings());
        assertFalse(reported.warnings().contains("b.sou"), reported.warnings());
    }

    @Test
    void aCleanSourceReportsNothing(@TempDir Path dir) throws IOException {
        Path source = ProcessorRun.write(dir, "clean.sou", """
                module demo

                data Eaches = Int
                    invariant value >= 0

                behavior wrap : (n: Eaches) -> Eaches
                    constructs Eaches
                let wrap (n) = Eaches(n.value)
                """);

        ProcessorRun reported = ProcessorRun.of(dir, source, "en");

        assertTrue(reported.ok(), reported.errors());
        assertTrue(reported.warnings().isBlank(), reported.warnings());
    }

}
