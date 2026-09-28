package souther.lsp.analysis;

import org.junit.jupiter.api.Test;
import souther.compiler.Compiler;
import souther.compiler.jvm.ClassFileImage;
import souther.compiler.jvm.JvmClassName;
import souther.lsp.protocol.CompletionItem;
import souther.lsp.protocol.Position;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A request between a change to the workspace and the next diagnose is answered from the workspace
 * as it now is.
 *
 * <p>The server answers a request that is waiting before it diagnoses, on purpose, so there is
 * such a gap after every change. What a request compiles against is then the workspace's sources
 * and the modules on its path, and the two have to be one reading of it: sources read now against a
 * path left over from the last diagnose is a workspace that never existed.
 */
class ARequestIsAnsweredFromTheWorkspaceAsItIsNowTest {

    private static final String LIB = """
            module lib.rule exposing ( double )

            let double (n: Int): Int = n * 2
            """;

    private static final String APP = """
            module app
            import lib.rule

            let twice (n: Int): Int = lib.rule.
            """;

    private static final String APP_URI = "file:///app.sou";

    @Test
    void aFolderAddedWithItsBuildIsReadByTheNextRequest() throws Exception {
        Path unbuilt = Files.createTempDirectory("ws");
        Path built = Files.createTempDirectory("ws");
        for (Map.Entry<String, ClassFileImage> c : Compiler.compileModules(List.of(LIB)).entrySet()) {
            Path file = built.resolve("build/classes/java/main").resolve(JvmClassName.classFile(c.getKey()));
            Files.createDirectories(file.getParent());
            Files.write(file, c.getValue().bytes());
        }
        Map<String, String> open = Map.of(APP_URI, APP);

        Workspace workspace = new Workspace();
        workspace.setRoots(List.of(unbuilt.toUri().toString()));
        Analyzer analyzer = new Analyzer();
        analyzer.diagnostics(workspace.snapshot(open));   // the compile is made against nothing built

        workspace.changeRoots(List.of(built.toUri().toString()), List.of(unbuilt.toUri().toString()));
        int line = (int) APP.lines().takeWhile(l -> !l.startsWith("let twice")).count();
        List<String> offered = analyzer.completions(APP_URI,
                        new Position(line, APP.lines().toList().get(line).length()),
                        workspace.snapshot(open)).stream()
                .map(CompletionItem::label).toList();

        assertTrue(offered.contains("double"),
                "the module the added folder built is what a dot after its name offers: " + offered);
    }
}
