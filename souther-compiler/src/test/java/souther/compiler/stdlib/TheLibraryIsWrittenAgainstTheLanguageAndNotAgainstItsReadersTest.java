package souther.compiler.stdlib;

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
 * The library's declarations say what the language means and nothing about who reads them.
 *
 * <p>Two halves of one rule. Nothing here may name a reader, so a reader of the library does not
 * take that reader with it — which is what putting the declarations inside the check did, and is
 * why {@code codegen}, {@code doc} and {@code examples} each depended on the whole of name
 * resolution to ask what {@code List.map} is (#1010). And nothing here may name a physical
 * representation, so what a backend does with a declaration stays that backend's: a second backend
 * answers the same declarations differently, and a fact recorded here that only one of them could
 * honour would be a fact about that backend wearing the library's name.
 *
 * <p>Written against the source and not against imports, so that naming a package outright — with
 * no import line to see — is caught too.
 */
class TheLibraryIsWrittenAgainstTheLanguageAndNotAgainstItsReadersTest {

    /** Everything that reads the library, and everything that reads what reads it. */
    private static final List<String> ITS_READERS = List.of(
            "souther.compiler.check",
            "souther.compiler.codegen",
            "souther.compiler.jvm",
            "souther.compiler.query",
            "souther.compiler.doc",
            "souther.compiler.examples",
            "souther.compiler.meta",
            "souther.compiler.derive",
            "souther.compiler.partition",
            "souther.compiler.evaluate",
            "souther.compiler.frontend",
            "souther.compiler.highlight");

    /** How a value is spelled on one machine. A {@code ClassDesc} is the JVM's, and the runtime
     *  namespace is the package one backend ships its hand-written classes in. */
    private static final List<String> ONE_BACKENDS_ANSWER = List.of(
            "ClassDesc", "MethodTypeDesc", "souther.runtime", "java.lang.constant");

    @Test
    void theLibraryNamesNothingThatReadsIt() throws IOException {
        List<String> naming = new ArrayList<>();
        for (Path source : sources()) {
            String text = Files.readString(source);
            for (String reader : ITS_READERS) {
                if (text.contains(reader)) {
                    naming.add(source.getFileName() + " names " + reader);
                }
            }
        }

        assertEquals(List.of(), naming,
                "the library's declarations are read by the check, by code generation and by"
                        + " documentation alike, and are written against none of them");
    }

    @Test
    void andSaysNothingAboutHowAnyOfItIsRepresented() throws IOException {
        List<String> naming = new ArrayList<>();
        for (Path source : sources()) {
            String text = Files.readString(source);
            for (String physical : ONE_BACKENDS_ANSWER) {
                if (text.contains(physical)) {
                    naming.add(source.getFileName() + " names " + physical);
                }
            }
        }

        assertEquals(List.of(), naming,
                "what a declaration means is the library's; what represents it is a backend's");
    }

    private static List<Path> sources() throws IOException {
        Path library = Path.of("src/main/java/souther/compiler/stdlib");
        assertTrue(Files.isDirectory(library), () -> "no " + library.toAbsolutePath());
        try (Stream<Path> walk = Files.walk(library)) {
            List<Path> found = walk.filter(each -> each.toString().endsWith(".java")).sorted()
                    .toList();
            assertTrue(found.size() > 1, () -> "the package is more than one file: " + found);
            return found;
        }
    }
}
