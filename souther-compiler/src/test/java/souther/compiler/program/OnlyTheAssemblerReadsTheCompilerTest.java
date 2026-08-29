package souther.compiler.program;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * One file in this package reads the compiler, and it is the one that takes the snapshot.
 *
 * <p>The other half of the boundary. What an output can reach is answered by walking the public API
 * ({@code NothingReachableFromACheckedProgramNamesTheCompilerTest}, which stands outside this
 * artifact); this answers what the model is written against. The two are different questions: a
 * field of a compiler-internal type is reachable by nothing public and still ties the snapshot to
 * the session it was taken from, and a convenience added to {@link CheckedBehavior} would begin the
 * erosion here rather than at the surface.
 *
 * <p>Written against the source and not the imports, so that naming a query outright —
 * {@code souther.compiler.query.Bodies.Checked} with no import to see — is caught too.
 */
class OnlyTheAssemblerReadsTheCompilerTest {

    /** How this compiler answers its own questions, what it emits with, and what it parsed into. */
    private static final List<String> THE_COMPILERS_OWN = List.of(
            "souther.compiler.query",
            "souther.compiler.codegen",
            "souther.compiler.ast");

    /** The one that materialises a snapshot out of a compilation, and so the one that reads it. */
    private static final String THE_ASSEMBLER = "CheckedProgramAssembler.java";

    @Test
    void onlyTheAssemblerNamesTheCompiler() throws IOException {
        List<String> naming = new ArrayList<>();
        List<String> read = new ArrayList<>();
        for (Path source : sources()) {
            read.add(source.getFileName().toString());
            if (source.getFileName().toString().equals(THE_ASSEMBLER)) {
                continue;
            }
            String text = Files.readString(source);
            for (String own : THE_COMPILERS_OWN) {
                if (text.contains(own)) {
                    naming.add(source.getFileName() + " names " + own);
                }
            }
        }

        assertTrue(read.contains(THE_ASSEMBLER),
                () -> "the assembler is what this exempts, and it was not among " + read);
        assertTrue(read.size() > 1, () -> "the package is more than the assembler: " + read);
        assertEquals(List.of(), naming,
                "the checked-program model is written against the language, not against this"
                        + " compiler; only the snapshot's assembler reads how it answers");
    }

    /**
     * And the assembler is the one that does read it, so the exemption above is exempting
     * something.
     *
     * <p>An exemption for a file that had stopped needing it would go on standing, and the day
     * something else in this package reached for a query the answer would be to add a second name
     * to the list — which is how a rule with one exception becomes a rule with several.
     */
    @Test
    void andTheAssemblerIsWhatNeedsTheExemption() throws IOException {
        Path assembler = sources().stream()
                .filter(each -> each.getFileName().toString().equals(THE_ASSEMBLER))
                .findFirst()
                .orElseThrow();

        assertTrue(Files.readString(assembler).contains("souther.compiler.query"),
                "the assembler reads the compilation; if it has stopped, this exemption should go");
    }

    private static List<Path> sources() throws IOException {
        Path model = Path.of("src/main/java/souther/compiler/program");
        assertTrue(Files.isDirectory(model), () -> "no " + model.toAbsolutePath());
        try (Stream<Path> walk = Files.walk(model)) {
            return walk.filter(each -> each.toString().endsWith(".java")).sorted().toList();
        }
    }
}
