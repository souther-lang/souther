package souther.lsp.analysis;

import org.junit.jupiter.api.Test;
import souther.compiler.Compiler;
import souther.compiler.jvm.ClassFileImage;
import souther.compiler.jvm.JvmClassName;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Abandonment;
import souther.compiler.query.Compilation;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * Classes a build writes into a class output that was already there are what the next diagnose
 * reads.
 *
 * <p>The directory existing before the build is the case that matters. Where the modules on the
 * path are is then the same before and after, and a compile kept between edits for as long as
 * nothing moved would go on answering from the classes it read the first time — an import the
 * build now resolves would stay underlined as naming no module.
 */
class AClassABuildWritesIsReadByTheNextDiagnoseTest {

    private static final String LIB = """
            module lib.rule exposing ( Code )

            data Code = Int
            """;

    private static final String APP = """
            module app
            import lib.rule ( Code )

            data Order = { code: Code }
            """;

    @Test
    void aModuleBuiltIntoAnOutputThatWasThereIsReadByTheNextDiagnose() throws Exception {
        Path root = Files.createTempDirectory("ws");
        Path output = Files.createDirectories(root.resolve("lib/build/classes/java/main"));
        Path app = Files.createDirectories(root.resolve("app")).resolve("app.sou");
        Files.writeString(app, APP);
        String uri = app.toUri().toString();

        Workspace workspace = new Workspace();
        workspace.setRoots(List.of(root.toUri().toString()));
        Analyzer analyzer = new Analyzer();
        assertFalse(analyzer.diagnostics(workspace.snapshot(Map.of())).get(uri).isEmpty(),
                "nothing is built yet, so the import names no module");

        List<String> written = new ArrayList<>();
        for (Map.Entry<String, ClassFileImage> built : Compiler.compileModules(List.of(LIB)).entrySet()) {
            Path file = output.resolve(JvmClassName.classFile(built.getKey()));
            Files.createDirectories(file.getParent());
            Files.write(file, built.getValue().bytes());
            written.add(file.toUri().toString());
        }
        workspace.filesChanged(written);

        assertEquals(List.of(), analyzer.diagnostics(workspace.snapshot(Map.of())).get(uri),
                "the build is read");
    }

    /** The probe keeps a compile of its own between requests, and holds it to the same thing. */
    @Test
    void theProbeStartsItsCompileAgainForModulesWrittenAgainInThePlaceTheyWere() {
        String text = "module m\ndata P = { x: Int }\nlet f (p: P): Int = p.\n";
        int cursor = text.lastIndexOf(".\n") + 1;
        SemanticProbe probe = new SemanticProbe();
        ModulesOnThePath before = new ModulesOnThePath(ModulePath.EMPTY, 1);

        Compilation first = probe.of(Map.of(), Set.of(), before, URI, text, cursor,
                Abandonment.NEVER).compilation();
        assertSame(first, probe.of(Map.of(), Set.of(), before, URI, text, cursor,
                Abandonment.NEVER).compilation(), "nothing on the path moved");
        assertNotSame(first, probe.of(Map.of(), Set.of(), new ModulesOnThePath(ModulePath.EMPTY, 2),
                URI, text, cursor, Abandonment.NEVER).compilation(),
                "the same place, written again");
    }

    private static final String URI = "file:///m.sou";
}
