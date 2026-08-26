package souther.compiler.stdlib;

import souther.compiler.DefaultStdlib;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.lang.classfile.ClassFile;
import java.lang.classfile.constantpool.PoolEntry;
import java.lang.classfile.constantpool.Utf8Entry;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The names the library publishes are written down where the library is described, and nowhere
 * else.
 *
 * <p>{@code souther.list} declares {@code foldFrom} and the library publishes it as
 * {@code List.foldFrom}: the alias belongs to the library and to nothing that reads it. A pass that
 * wrote one out — to recognise the walk it lowers as a loop, to find the empty map a fold starts
 * from — was deciding what the library calls its own operations, and went on being right for
 * exactly as long as the two spellings agreed.
 *
 * <p>What such a pass wants is the operation, and it has one to hand: a call carries which kernel it
 * reaches, and what the library publishes as its walk the library answers ({@link Stdlib#theWalk}).
 * So the rule is that the spelling is not written outside here — and the compiled constant pools
 * are where a written one shows, whatever route the source took to it.
 *
 * <p>Read off the library's own published surface rather than a list kept here, so an operation the
 * library gains is covered without anybody remembering to add it.
 */
class NobodyOutsideTheLibrarySpellsWhatItPublishesTest {

    private static final Path COMPILED = Path.of("target", "classes", "souther", "compiler");

    /**
     * Where a published name may be written.
     *
     * <p>The library itself, which is what publishes them. The documentation reader, which quotes
     * the library's surface to a person. The semantic facts, which are statements about named
     * operations and are the library's own vocabulary written down beside it — this one is worth
     * moving and is not what this rule was written for.
     */
    private static final Set<String> MAY_SPELL_THEM = Set.of(
            "souther.compiler.stdlib.",
            "souther.compiler.doc.",
            "souther.compiler.semantics.OperationFacts");

    @Test
    void nothingOutsideTheLibraryWritesAPublishedNameOut() {
        Set<String> published = DefaultStdlib.get().published();
        assertTrue(published.size() > 20, () -> "read only " + published.size() + " published names");

        List<String> spelling = new ArrayList<>();
        List<Path> classes = compiledClasses();
        assertTrue(classes.size() > 100, () -> "read only " + classes.size() + " compiled classes");

        for (Path each : classes) {
            String owner = ownerOf(each);
            if (MAY_SPELL_THEM.stream().anyMatch(owner::startsWith)) {
                continue;
            }
            for (PoolEntry entry : constantPoolOf(each)) {
                if (entry instanceof Utf8Entry utf8 && published.contains(utf8.stringValue())) {
                    spelling.add(owner + " writes `" + utf8.stringValue() + "`");
                }
            }
        }

        assertEquals(List.of(), spelling.stream().sorted().distinct().toList(),
                "the library publishes these under aliases of its own; ask it which operation you"
                        + " mean, or ask the call which kernel it reaches");
    }

    private static String ownerOf(Path each) {
        return COMPILED.getParent().getParent().relativize(each).toString()
                .replace(java.io.File.separatorChar, '.')
                .replaceFirst("\\.class$", "")
                .replaceFirst("\\$.*$", "");
    }

    private static List<Path> compiledClasses() {
        try (Stream<Path> found = Files.walk(COMPILED)) {
            return found.filter(p -> p.toString().endsWith(".class")).sorted().toList();
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    private static Iterable<PoolEntry> constantPoolOf(Path each) {
        try {
            return ClassFile.of().parse(each).constantPool();
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }
}
