package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.HumanRenderer;
import souther.compiler.diag.SourceContext;
import souther.compiler.diag.SourcePos;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An error in a multi-file compile says which file it came from. A position is a line and a column,
 * so without the module it belongs to there is nothing to quote — the linker tags the error with the
 * source it was compiling, and the caller turns that into the file it read.
 */
class MultiFileDiagnosticOriginTest {

    private static final String A = """
            module a exposing ( 従業員ID )
            data 従業員ID = String
            """;

    private static final String B = """
            module b
            import a ( 従業員ID )
            data Out = { v: Int }
            behavior f : (who: 従業員ID) -> Out
                constructs Out
            let f (who) = Out { v = who }
            """;

    @Test
    void theErrorIsTaggedWithTheSourceItCameFrom() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(A, B)));

        assertEquals(1, e.sourceIndex(), "the error is in the second source");
    }

    @Test
    void anErrorInTheFirstSourceIsTaggedToo() {
        String broken = """
                module a exposing ( 従業員ID )
                data 従業員ID = String
                data Bad = { v: Nonexistent }
                """;

        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(broken, B)));

        assertEquals(0, e.sourceIndex());
    }

    @Test
    void aSingleModuleCompileCarriesNoOrigin() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module solo
                data Out = { v: Int }
                behavior f : (s: String) -> Out
                    constructs Out
                let f (s) = Out { v = s }
                """));

        assertEquals(-1, e.sourceIndex(), "there is only one source; the caller knows which");
    }

    @Test
    void aModuleWithAnAttachedExampleFileStillNamesItsOwnBodyError() {
        String target = """
                module t
                data Out = { v: Int }
                behavior f : (s: String) -> Out
                    constructs Out
                let f (s) = Out { v = s }
                """;
        String examples = """
                examples for t
                example f
                    | "one" : ("a") -> Out { v = 1 }
                """;

        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(target, examples)));

        assertEquals(0, e.sourceIndex(), "the type error is in the module's own body");
    }

    @Test
    void aFailingExampleInAMergedModuleNamesNoSource() {
        String target = """
                module t
                data Out = { v: Int }
                behavior f : (n: Int) -> Out
                    constructs Out
                let f (n) = Out { v = n }
                """;
        String examples = """
                examples for t
                example f
                    | "wrong" : (1) -> Out { v = 2 }
                """;

        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(target, examples)));

        assertEquals(-1, e.sourceIndex(),
                "the example was written in the other file, so neither file's line is quoted");
    }

    @Test
    void theCliPicksTheFileTheErrorCameFrom(@TempDir Path dir) throws IOException {
        Path a = dir.resolve("a.sou");
        Path b = dir.resolve("b.sou");
        Files.writeString(a, A);
        Files.writeString(b, B);

        CompileException e = assertThrows(CompileException.class,
                () -> Main.compileToDir(List.of(a, b), dir.resolve("out")));

        assertEquals(b, Main.sourceOf(List.of(a, b), e));
    }

    @Test
    void anUntaggedMultiFileErrorStillRendersWithoutASnippet(@TempDir Path dir) {
        Path a = dir.resolve("a.sou");
        Path b = dir.resolve("b.sou");
        CompileException untagged = new CompileException(new SourcePos(1, 1), "boom");

        assertNull(Main.sourceOf(List.of(a, b), untagged));
    }

    @Test
    void theRenderedErrorQuotesTheRightFile(@TempDir Path dir) throws IOException {
        Path a = dir.resolve("a.sou");
        Path b = dir.resolve("b.sou");
        Files.writeString(a, A);
        Files.writeString(b, B);

        CompileException e = assertThrows(CompileException.class,
                () -> Main.compileToDir(List.of(a, b), dir.resolve("out")));
        Path source = Main.sourceOf(List.of(a, b), e);
        String rendered = new HumanRenderer(false).render(e.diagnostic(),
                new SourceContext(source.getFileName().toString(), Files.readString(source)),
                Locale.ENGLISH);

        assertTrue(rendered.contains("b.sou:6:"), rendered);
        assertTrue(rendered.contains("let f (who) = Out { v = who }"), rendered);
    }
}
