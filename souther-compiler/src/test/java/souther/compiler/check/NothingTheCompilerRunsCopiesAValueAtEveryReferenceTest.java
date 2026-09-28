package souther.compiler.check;

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
 * No inliner the compiler makes for a program copies a value's body at every reference.
 *
 * <p>A value denotes as if its body stood at each reference, and a value that names another twice,
 * over a chain of them, is a tree that doubles at each link when its body is copied at each. What
 * a reader of the tree needs is a tree that holds each value once, where it is demanded, and every
 * reader the compiler has can read one. The choice is made where an inliner is made, and a reader
 * that was given the copying one because it looked as if it only wanted shapes is a reader that
 * answers exactly as slowly as the source it is handed is long, until the source is a chain.
 *
 * <p>An inliner that copies is one a test makes to hold what copying does. A place in the compiler
 * that needs one is a place to say why here, and to add itself to this.
 */
class NothingTheCompilerRunsCopiesAValueAtEveryReferenceTest {

    /** What a source writes to make an inliner that copies. */
    private static final String COPYING = "ValueAtAReference.COPIED";

    @Test
    void noInlinerTheCompilerMakesCopies() throws IOException {
        Path main = Path.of("src/main/java/souther/compiler");
        assertTrue(Files.isDirectory(main), () -> "no " + main.toAbsolutePath());
        List<String> making = new ArrayList<>();
        try (Stream<Path> walk = Files.walk(main)) {
            for (Path source : walk.filter(each -> each.toString().endsWith(".java")).sorted()
                    .toList()) {
                if (Files.readString(source).contains(COPYING)) {
                    making.add(main.relativize(source).toString());
                }
            }
        }

        assertEquals(List.of(), making,
                "an inliner made to copy a value at every reference is exponential in a chain of"
                        + " values that each name the one before them twice; make it share each"
                        + " value per region, or say here why this one may not");
    }
}
