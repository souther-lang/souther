package souther.build.driver;

import souther.build.BuildDiagnostic;
import souther.build.BuildRequest;
import souther.build.BuildResult;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

class CompilerBuildDriverTest {

    @Test
    void aModuleUnderTheSourceDirectoryIsCompiledToTheOutputDirectory(@TempDir Path dir)
            throws IOException {
        Path sources = Files.createDirectories(dir.resolve("src"));
        Files.writeString(sources.resolve("money.sou"), """
                module shared.money exposing ( Amount )
                data Amount = Int
                    invariant value >= 0
                """);
        Path classes = dir.resolve("classes");

        BuildResult result = new CompilerBuildDriver()
                .compile(new BuildRequest(List.of(sources), List.of(), classes, "en"));

        assertTrue(result.succeeded(), () -> String.valueOf(result.diagnostics()));
        assertTrue(Files.exists(classes.resolve("shared/money/Amount.class")),
                "the generated classes go under the output directory the request named");
    }

    /**
     * The positive half of {@link #aCompileErrorComesBackRenderedRatherThanRaised}: the same import
     * resolves when the depended-on project's classes are on the request's class path, which is
     * where depending on its jar already puts them.
     */
    @Test
    void anImportResolvesAgainstTheClassesOnTheRequestsClassPath(@TempDir Path dir)
            throws IOException {
        Path libClasses = compiled(dir, "lib", """
                module shared.money exposing ( Amount )
                data Amount = Int
                    invariant value >= 0
                """, List.of());

        Path appClasses = compiled(dir, "app", """
                module app.order exposing ( Order )
                import shared.money ( Amount )
                data Order = { total: Amount }
                """, List.of(libClasses));

        assertTrue(Files.exists(appClasses.resolve("app/order/Order.class")));
        assertFalse(Files.exists(appClasses.resolve("shared/money/Amount.class")),
                "the dependency's classes belong to its own build");
    }

    /** One project's build: its source compiled with {@code classPath} behind it. */
    private static Path compiled(Path dir, String project, String source, List<Path> classPath)
            throws IOException {
        Path sources = Files.createDirectories(dir.resolve(project).resolve("src"));
        Files.writeString(sources.resolve("module.sou"), source);
        Path classes = dir.resolve(project).resolve("classes");

        BuildResult result = new CompilerBuildDriver()
                .compile(new BuildRequest(List.of(sources), classPath, classes, "en"));

        assertTrue(result.succeeded(), () -> project + ": " + result.diagnostics());
        return classes;
    }

    /**
     * A single source with no {@code module} header is a self-contained module: it can import
     * nothing, and it is not a module set of one. The compiler is asked differently for it, which is
     * a distinction a build has no way to make itself.
     */
    @Test
    void aLoneSourceWithNoModuleHeaderIsCompiledAsASelfContainedModule(@TempDir Path dir)
            throws IOException {
        Path sources = Files.createDirectories(dir.resolve("src"));
        Files.writeString(sources.resolve("amount.sou"), """
                data Amount = Int
                    invariant value >= 0
                """);
        Path classes = dir.resolve("classes");

        BuildResult result = new CompilerBuildDriver()
                .compile(new BuildRequest(List.of(sources), List.of(), classes, "en"));

        assertTrue(result.succeeded(), () -> String.valueOf(result.diagnostics()));
        assertTrue(Files.exists(classes.resolve("Main/Amount.class")),
                "named the way the annotation processor names one, so the same source compiles the "
                        + "same way whichever integration a project uses");
    }

    /** One unproven construction, on line 10. */
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
    void anUnprovenConstructionComesBackAsAWarningAndTheBuildGoesOn(@TempDir Path dir)
            throws IOException {
        Path sources = Files.createDirectories(dir.resolve("src"));
        Files.writeString(sources.resolve("demo.sou"), UNPROVEN);
        Path classes = dir.resolve("classes");

        BuildResult result = new CompilerBuildDriver()
                .compile(new BuildRequest(List.of(sources), List.of(), classes, "en"));

        assertTrue(result.succeeded(), () -> String.valueOf(result.diagnostics()));
        assertEquals(1, result.diagnostics().size(), () -> String.valueOf(result.diagnostics()));
        BuildDiagnostic warning = result.diagnostics().get(0);
        assertEquals(BuildDiagnostic.Severity.WARNING, warning.severity());
        assertTrue(warning.rendered().contains("E2011"), warning.rendered());
        assertTrue(warning.rendered().contains("demo.sou:10:5"),
                "the snippet carries the position, which is inside a file the build has no other "
                        + "way to point at: " + warning.rendered());
    }

    @Test
    void theRequestsLanguageIsTheLanguageTheDiagnosticIsWrittenIn(@TempDir Path dir)
            throws IOException {
        Path sources = Files.createDirectories(dir.resolve("src"));
        Files.writeString(sources.resolve("demo.sou"), UNPROVEN);

        BuildResult result = new CompilerBuildDriver().compile(
                new BuildRequest(List.of(sources), List.of(), dir.resolve("classes"), "ja"));

        String rendered = result.diagnostics().get(0).rendered();
        assertTrue(rendered.contains("(警告)"), rendered);
        assertTrue(rendered.contains("不変条件に違反する可能性があります"), rendered);
    }

    @Test
    void aCompileErrorComesBackRenderedRatherThanRaised(@TempDir Path dir) throws IOException {
        Path sources = Files.createDirectories(dir.resolve("src"));
        Files.writeString(sources.resolve("order.sou"), """
                module app.order
                import shared.money ( Amount )
                data Order = { total: Amount }
                """);

        BuildResult result = new CompilerBuildDriver().compile(
                new BuildRequest(List.of(sources), List.of(), dir.resolve("classes"), "en"));

        assertFalse(result.succeeded());
        List<BuildDiagnostic> errors = result.diagnostics().stream()
                .filter(d -> d.severity() == BuildDiagnostic.Severity.ERROR).toList();
        assertEquals(1, errors.size(), () -> String.valueOf(result.diagnostics()));
        assertTrue(errors.get(0).rendered().contains("shared.money"),
                () -> "the import that is wrong is named: " + errors.get(0).rendered());
    }
}
