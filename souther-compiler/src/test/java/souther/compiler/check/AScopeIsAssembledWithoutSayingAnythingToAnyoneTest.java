package souther.compiler.check;

import souther.compiler.diag.EveryShippedMessageCatalogIsCompleteAndValidTest;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Assembling a module's scope makes no diagnostics.
 *
 * <p>Two readers assemble one, and only one of them is talking to an author. A compilation tells
 * whoever wrote the import line; a reader putting published classes back together has nobody to
 * tell, and what a refused import means to it is that the module cannot be read here. A walk that
 * built diagnostics could only be used by the second reader by having it make things to say to
 * nobody and then count them — so what the walk answers with is a {@link Scoping.Refusal}, and
 * turning one into something to say is the compilation's, where it reads the result.
 *
 * <p>Held against the source rather than against behaviour, because what is being kept out is a
 * dependency. Nothing goes wrong the day someone reaches for {@code Diagnostic} here; what goes
 * wrong is later, when the second reader cannot use the rule that came with it.
 */
class AScopeIsAssembledWithoutSayingAnythingToAnyoneTest {

    /** The names of the things a reader is told with. {@code CompileException} is one of them: it
     *  carries a diagnostic, and throwing one is saying it to whoever asked. */
    private static final List<String> SAYING =
            List.of("Diagnostic", "CompileException", "Report", "Message");

    /** What the scope of a module is derived from, and where it is derived. */
    private static final List<String> ASSEMBLY = List.of("Scoping.java", "ModuleUniverse.java");

    @Test
    void theAssemblyNamesNothingAReaderIsToldWith() throws IOException {
        Set<String> reaching = new LinkedHashSet<>();
        for (Path source : sources()) {
            String text = Files.readString(source);
            for (String said : SAYING) {
                if (text.contains(said)) {
                    reaching.add(source.getFileName() + ": " + said);
                }
            }
        }

        assertEquals(Set.of(), reaching,
                "a scope is assembled for two readers, and only one of them has anyone to tell");
    }

    /** The assembly's own sources — asked for by name, and each one has to be there. A file that
     *  moved would otherwise leave this passing over nothing. */
    private static List<Path> sources() throws IOException {
        List<Path> found = EveryShippedMessageCatalogIsCompleteAndValidTest.mainSources().stream()
                .filter(p -> ASSEMBLY.contains(p.getFileName().toString()))
                .toList();
        assertEquals(ASSEMBLY.size(), found.size(),
                () -> "every source the scope is assembled in is read: " + found);
        assertTrue(found.stream().allMatch(Files::isRegularFile), found::toString);
        return found;
    }
}
