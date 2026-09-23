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
 * <p>Held over the source with its comments taken out, so an import, a fully qualified mention and
 * the string a backend's own table is written with are each caught, while an account of why the
 * dependency is refused is not one.
 */
class TheRuntimePackageIsTheBackendsToNameTest {

    /** The package this is about, spelled the way a Java source spells it — in an import, in a
     *  fully qualified name, and inside the string one backend's table maps an identity to. */
    private static final String RUNTIME = "souther.runtime";

    /**
     * Where a declaration's identity, its scope, its rules, its readings and the arithmetic those
     * rules are reasoned in live. None of them is about a machine.
     */
    private static final Set<String> TARGET_NEUTRAL =
            Set.of("types", "check", "stdlib", "semantics", "partition", "inputs", "core", "flow",
                    "numeric");

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
                    && code(Files.readString(source)).contains(RUNTIME)) {
                naming.add(relative(source));
            }
        }

        assertEquals(List.of(), naming.stream().sorted().toList(),
                "what a declaration is and what one backend calls it are two things; the second is"
                        + " `jvm.SoutherJvmAbi`'s to say and is said there");
    }

    /**
     * And what a backend writes into a program is never the exact arithmetic's package.
     *
     * <p>{@code souther.exact} is target-neutral and shipped in the runtime artifact, which is what lets
     * the compiler reason with the arithmetic a program runs. It is an implementation both share and no
     * part of the language's vocabulary or of a class a backend generates, so a program links against
     * {@code souther.runtime} alone and the arithmetic stays replaceable behind it.
     */
    @Test
    void nothingABackendWritesNamesTheExactPackage() throws IOException {
        Set<String> naming = new LinkedHashSet<>();
        for (Path source : sources()) {
            if (MAY_NAME_IT.contains(area(source))
                    && code(Files.readString(source)).contains("souther.exact")) {
                naming.add(relative(source));
            }
        }

        assertEquals(List.of(), naming.stream().sorted().toList(),
                "a generated class reaches the arithmetic through souther.runtime, never past it");
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

    /**
     * What the reading keeps and what it drops, held against a source written to carry both.
     *
     * <p>The rule above is one predicate over what this hands back, so a hole here is a hole the
     * rule cannot show. What it has to get right is the difference between a dependency on the
     * package and an account of why there is none: the first is an import, a fully qualified name or
     * the string a table is written with, the second is a comment — and two of the target-neutral
     * areas carry one, so dropping the distinction makes the account the finding.
     *
     * <p>The text block carries an unpaired quote, which is what tells a reading that knows about
     * text blocks from one that walks quotes in pairs. To the second, the line under that quote is
     * outside any string, so its {@code //} starts a comment and the package named there goes —
     * which is a dependency dropped rather than an account kept.
     */
    @Test
    void whatTheReadingKeepsIsWhatTheCompilerReads() {
        String source = """
                package souther.compiler.check;

                import souther.runtime.Fn;

                /** Why {@code souther.runtime} is not named here. */
                final class One {
                    // and souther.runtime again
                    private static final String ABI = "souther.runtime";
                    private final souther.runtime.Fn held = null;
                    private static final String SLASHES = "// not a comment souther.runtime";
                    private static final String BLOCK = ""\"
                            say "hi
                            // nor here, in souther.runtime
                            ""\";
                }
                """;

        String read = code(source);

        assertEquals(5, howOftenItNames(read),
                () -> "the import, the fully qualified name and the three strings are kept and the"
                        + " two comments are dropped: " + read);
        assertTrue(read.contains("import souther.runtime.Fn;"), read);
        assertTrue(read.contains("\"souther.runtime\""), read);
        assertTrue(read.contains("private final souther.runtime.Fn held"), read);
        assertTrue(read.contains("\"// not a comment souther.runtime\""), read);
        assertTrue(read.contains("say \"hi"), read);
        assertTrue(read.contains("// nor here, in souther.runtime"), read);
        assertTrue(!read.contains("Why") && !read.contains("again"), read);
    }

    /** How often a reading still names the package. */
    private static int howOftenItNames(String read) {
        int found = 0;
        for (int at = read.indexOf(RUNTIME); at >= 0; at = read.indexOf(RUNTIME, at + 1)) {
            found++;
        }
        return found;
    }

    /**
     * The source with its comments taken out and its strings left in.
     *
     * <p>Strings stay because one of them is the dependency: a layer writing the package's name into
     * a table of its own is stating a physical name, which is what this rule was written for.
     * Comments go because the two things read alike in the text and say opposite things.
     */
    private static String code(String source) {
        StringBuilder out = new StringBuilder(source.length());
        int at = 0;
        while (at < source.length()) {
            char here = source.charAt(at);
            if (source.startsWith("//", at)) {
                while (at < source.length() && source.charAt(at) != '\n') {
                    at++;
                }
            } else if (source.startsWith("/*", at)) {
                int ends = source.indexOf("*/", at + 2);
                at = ends < 0 ? source.length() : ends + 2;
            } else if (source.startsWith("\"\"\"", at)) {
                int ends = source.indexOf("\"\"\"", at + 3);
                int to = ends < 0 ? source.length() : ends + 3;
                out.append(source, at, to);
                at = to;
            } else if (here == '"' || here == '\'') {
                int to = at + 1;
                while (to < source.length() && source.charAt(to) != here) {
                    to += source.charAt(to) == '\\' ? 2 : 1;
                }
                to = Math.min(to + 1, source.length());
                out.append(source, at, to);
                at = to;
            } else {
                out.append(here);
                at++;
            }
        }
        return out.toString();
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
