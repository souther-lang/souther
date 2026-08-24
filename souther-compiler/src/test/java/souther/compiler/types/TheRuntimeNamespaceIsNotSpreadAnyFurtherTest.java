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
 * The namespace the language's own declarations are addressed under is spelled
 * {@code souther.runtime}, which is the package one backend ships their classes in. Nothing new may
 * read it.
 *
 * <p>A debt with a name. What the language declares — {@code RoundingMode}, and the error cases
 * {@code DivisionByZero} and {@code NotANumber} beside it — has a semantic identity, and that
 * identity is currently written as the JVM package their implementations live in. So the mapping
 * from what a declaration <em>is</em> to what it is <em>called on a machine</em> is the identity
 * function, and there is no place for a second backend to give a different answer.
 *
 * <p>Not repaired here, because the spelling reaches the class files this compiler writes and the
 * classes souther-runtime ships; it is its own issue. What is held here is that it does not spread
 * while that issue is open: the readers are written out, and a new one fails this rather than
 * arriving unremarked and making the repair larger.
 *
 * <p>Held over the source rather than over imports, so a fully qualified mention is caught too. It
 * counts the readers and not the definition: {@code types.TypeSymbol} is where the namespace is
 * written down and where an identity under it is minted, which is the one place that should name it.
 */
class TheRuntimeNamespaceIsNotSpreadAnyFurtherTest {

    /** The files that address a declaration under the runtime namespace, and what each wants of it. */
    private static final Set<String> KNOWN = Set.of(
            // The library, which anchors what it declares to it.
            "stdlib/Stdlib.java",
            "check/StdlibLoader.java",
            // What a name written in a module means, and what an identity is a declaration of.
            "check/TypeScope.java",
            "check/Declarations.java",
            // The JVM's answer for such a declaration, which is where the mapping belongs.
            "jvm/SoutherJvmAbi.java",
            // A kernel taking one names its class, and asks the ABI above for it.
            "codegen/Intrinsics.java",
            // A rule about rounding, which names the declaration it is about. ADR-0087 says no
            // place outside the registration may branch on the type's name; this one does, and is
            // part of the same debt.
            "semantics/Arithmetic.java");

    @Test
    void nothingElseAddressesADeclarationUnderTheRuntimeNamespace() throws IOException {
        Set<String> reading = new LinkedHashSet<>();
        for (Path source : sources()) {
            String text = Files.readString(source);
            if (text.contains("TypeSymbol.RUNTIME") || text.contains("TypeSymbol.runtime(")) {
                reading.add(relative(source));
            }
        }

        assertEquals(KNOWN.stream().sorted().toList(), reading.stream().sorted().toList(),
                "a semantic identity and the class a backend gives it are two things; until they"
                        + " are told apart, the places that read them as one are these and no more");
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
