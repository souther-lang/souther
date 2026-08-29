package souther.compiler;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Who may reach for the process's library, and who is handed one.
 *
 * <p>Two kinds of caller and no others. A <b>boundary</b> begins a piece of work and settles what
 * that work is held to: {@code Compilation} reads the library as it starts, beside the evaluation
 * policy and the reading policy it reads there for the same reason, and everything it reaches takes
 * a value. A <b>process constant</b> turns the shipped library into a rule table this compiler
 * checks with — the same table under every compilation and under any backend — so threading one in
 * would put a parameter through a dozen signatures to say something none of them varies in.
 *
 * <p>Everything else takes a {@link souther.compiler.stdlib.Stdlib} as a value, because what it
 * answers depends on which compilation is asking. {@code TypeScope}, {@code Declarations},
 * {@code Resolve} and {@code CallElaborator} are the ones that used to reach for a static and are
 * the reason this exists.
 *
 * <p>The set is compared whole rather than counted. A count lets one name be dropped and another
 * added and says nothing about it, which is exactly the edit this is here to catch.
 */
class OnlyABoundaryOrAProcessConstantReadsTheDefaultLibraryTest {

    /** Where a piece of work begins and settles what it is held to. */
    private static final Set<String> BOUNDARIES = Set.of(
            // A compile: read once as it starts, and handed to everything it reaches.
            "query/Compilation.java",
            // `souther api`, which lists the library and is downstream of no compile.
            "doc/ApiCommand.java");

    /** Rule tables derived from the shipped library and from nothing else. */
    private static final Set<String> PROCESS_CONSTANTS = Set.of(
            "check/Combinators.java",
            "check/Preserved.java",
            "check/Reductions.java",
            "check/DischargeRules.java");

    /** What building a library must not need, because it is what building one produces. */
    private static final List<String> WHAT_THE_LOADER_MAY_NOT_READ = List.of(
            "DefaultStdlib", "Combinators", "Preserved", "Accumulations", "Reductions",
            "DischargeRules");

    @Test
    void theseAreTheOnlyReadersOfTheProcessLibrary() throws IOException {
        Set<String> reading = new LinkedHashSet<>();
        for (Path source : sources()) {
            if (Files.readString(source).contains("DefaultStdlib.get()")) {
                reading.add(relative(source));
            }
        }

        Set<String> allowed = new LinkedHashSet<>(BOUNDARIES);
        allowed.addAll(PROCESS_CONSTANTS);
        assertEquals(allowed.stream().sorted().toList(), reading.stream().sorted().toList(),
                "a reader that depends on which compilation is running takes a Stdlib as a value;"
                        + " only a boundary and a rule table derived from the shipped library alone"
                        + " may read the process's own");
    }

    /**
     * And the loader reads none of them.
     *
     * <p>The one ordering this arrangement can still get wrong. A rule table is derived from a
     * finished library, and building a library that read one would be asking for the library while
     * the library is being read — the class-initializer cycle the loader was split out to end,
     * arriving back through the other side.
     */
    @Test
    void andBuildingALibraryNeedsNoneOfThem() throws IOException {
        Path loader = Path.of("src/main/java/souther/compiler/check/StdlibLoader.java");
        assertTrue(Files.isRegularFile(loader), () -> "no " + loader.toAbsolutePath());
        String text = Files.readString(loader);

        List<String> reached = WHAT_THE_LOADER_MAY_NOT_READ.stream()
                .filter(text::contains).toList();
        assertEquals(List.of(), reached,
                "the loader builds a library out of sources and hands it over finished; a rule"
                        + " table it read would be one derived from the library it is still reading");
    }

    private static String relative(Path source) {
        String path = source.toString().replace('\\', '/');
        return path.substring(path.indexOf("souther/compiler/") + "souther/compiler/".length());
    }

    private static List<Path> sources() throws IOException {
        Path main = Path.of("src/main/java/souther/compiler");
        assertTrue(Files.isDirectory(main), () -> "no " + main.toAbsolutePath());
        try (Stream<Path> walk = Files.walk(main)) {
            List<Path> found = walk.filter(each -> each.toString().endsWith(".java")).sorted()
                    .toList();
            assertTrue(found.size() > 100, () -> "that is not the compiler: " + found.size());
            return found;
        }
    }
}
