package souther.compiler.types;

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
 * {@code souther.runtime} is a JVM package, and only the parts of this compiler that answer for the
 * JVM may name it.
 *
 * <p>It used to be both: the package souther-runtime ships its hand-written classes in, and the
 * namespace the language's own declarations were addressed under. So a semantic identity and a
 * physical one were the same string, the mapping between them was the identity function, and there
 * was nothing for a second backend to answer differently — the question was settled by how the name
 * was spelled (#1038).
 *
 * <p>They are two things now. {@code souther.decimal} declares {@code RoundingMode}; that this
 * backend represents it as {@code souther.runtime.RoundingMode} is an entry in a table in
 * {@code jvm.SoutherJvmAbi}, and a backend that generated the declaration instead would write a
 * different one. What is held here is that the string does not travel back: a layer that reasons
 * about what a declaration <em>is</em> may not name the package one backend keeps it in.
 *
 * <p>Held over the source rather than over imports, so a fully qualified mention is caught too.
 */
class TheRuntimePackageIsTheBackendsToNameTest {

    /**
     * Where a declaration's identity, its scope, its rules and its readings live. None of them is
     * about a machine.
     */
    private static final Set<String> TARGET_NEUTRAL =
            Set.of("types", "check", "stdlib", "semantics", "partition", "inputs", "core", "flow");

    /**
     * And where naming it is the job. {@code jvm} maps an identity to a physical name;
     * {@code codegen} writes the classes and names the runtime's own support classes it calls into;
     * {@code meta} reads and writes class-file annotations, whose types are runtime classes.
     */
    private static final Set<String> MAY_NAME_IT = Set.of("jvm", "codegen", "meta", "examples",
            "generated");

    @Test
    void nothingThatReasonsAboutDeclarationsNamesTheRuntimePackage() throws IOException {
        Set<String> naming = new LinkedHashSet<>();
        for (Path source : sources()) {
            String area = area(source);
            if (TARGET_NEUTRAL.contains(area)
                    && Files.readString(source).contains("\"souther.runtime\"")) {
                naming.add(relative(source));
            }
        }

        assertEquals(List.of(), naming.stream().sorted().toList(),
                "what a declaration is and what one backend calls it are two things; the second is"
                        + " `jvm.SoutherJvmAbi`'s to say and is said there");
    }

    /** And the areas above are areas: a package renamed out from under this stops covering what it
     *  covered, and would do it silently. */
    @Test
    void everyAreaNamedHereIsAPackageOfTheCompiler() throws IOException {
        Set<String> areas = new LinkedHashSet<>();
        for (Path source : sources()) {
            areas.add(area(source));
        }

        Set<String> named = new LinkedHashSet<>(TARGET_NEUTRAL);
        named.addAll(MAY_NAME_IT);
        assertEquals(List.of(), named.stream().filter(each -> !areas.contains(each)).sorted().toList(),
                "an area named here is no package of this compiler");
    }

    /** The package directly under {@code souther/compiler}, or the empty string for a source
     *  sitting there. */
    private static String area(Path source) {
        String path = relative(source);
        int slash = path.indexOf('/');
        return slash < 0 ? "" : path.substring(0, slash);
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
