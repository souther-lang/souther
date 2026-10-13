package souther.compiler.program;

import org.junit.jupiter.api.Test;
import souther.compiler.CompilationSources;
import souther.compiler.CompilationSources.SourceFile;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.DiagnosticRenderer;
import souther.compiler.diag.HumanRenderer;
import souther.compiler.meta.ModulePath;

import java.util.List;
import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A program an output checks from the files a command was handed is the program
 * {@code souther compile} checks from them.
 *
 * <p>A lone file may omit its header and is then the module its file names (spec {@code #modules},
 * ADR-0043). An output that could hand over only texts could check such a file as nothing: every
 * text it handed over had to name itself, so the file {@code souther compile} takes was refused.
 * And a refusal is quoted from the same sources it was checked from, so the place a report names is
 * the place in the text that was checked.
 */
class AProgramCheckedFromFilesIsTheOneSoutherCompileChecksTest {

    private static final String HEADERLESS = """
            behavior next : (n: Int) -> Int

            let next (n) = n + 1
            """;

    @Test
    void aLoneFileWithNoHeaderIsTheModuleItsFileNames() {
        CheckedProgram program = CheckedProgram.of(
                CompilationSources.files(List.of(new SourceFile("src/counting.sou", HEADERLESS))),
                ModulePath.EMPTY);

        assertNotNull(program.module("counting"),
                () -> "checked " + program.modules().stream().map(CheckedModule::name).toList());
    }

    @Test
    void textsStillHaveToNameThemselves() {
        assertThrows(CompileException.class, () -> CheckedProgram.of(List.of(HEADERLESS)));
    }

    @Test
    void aRefusalIsQuotedFromTheSourcesItWasCheckedFrom() {
        CompilationSources sources = CompilationSources.files(List.of(
                new SourceFile("a/model.sou", """
                        module a

                        behavior fine : (n: Int) -> Int

                        let fine (n) = n + 1
                        """),
                new SourceFile("b/model.sou", """
                        module b

                        behavior broken : (n: Int) -> Int

                        let broken (n) = n + missing
                        """)));

        CompileException refused = assertThrows(CompileException.class,
                () -> CheckedProgram.of(sources, ModulePath.EMPTY));
        String said = String.join("\n", DiagnosticRenderer.renderAll(refused.locatedDiagnostics(),
                sources.contexts(), new HumanRenderer(false), Locale.ENGLISH));

        assertTrue(said.contains("b/model.sou:5:22"), said);
        assertTrue(said.contains("let broken (n) = n + missing"), said);
        assertEquals(-1, said.indexOf("let fine"), said);
    }
}
