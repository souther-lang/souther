package souther.compiler.doc;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A code is what a diagnostic hands the reader to go and look the thing up with. Every code the
 * compiler prints therefore has to resolve, or the reader is handed a name and then told there is
 * nothing under it — which is worse than printing no code at all, since they spend the lookup
 * first.
 *
 * <p>What is checked is that the lookup answers, not that the codes and the sections are the same
 * set. Several diagnostics coming out of one language feature are explained together, and a section
 * carrying the codes of all of them is a section doing its job; what would be wrong is a code with
 * no way to reach the section that explains it.
 *
 * <p>The codes are discovered from {@code E}-and-four-digits string literals in every module's main
 * sources. That is the domain this quantifies over: a code assembled at run time out of pieces is
 * outside it and would not be seen. Every code the compiler emits today is written as a literal at
 * the site that emits it.
 */
class EveryDiagnosticTheCompilerEmitsCanBeLookedUpTest {

    private static final Pattern CODE = Pattern.compile("\"(E[0-9]{4})\"");

    @Test
    void everyCodeTheCompilerPrintsResolvesToASection() throws IOException {
        SpecDocument spec = SpecDocument.bundled();
        Set<String> emitted = emittedCodes();
        Set<String> unresolved = new TreeSet<>();
        for (String code : emitted) {
            if (spec.section(code) == null) {
                unresolved.add(code);
            }
        }

        assertFalse(emitted.isEmpty(), "found no diagnostic code at all — the source scan missed the tree");
        assertEquals(Set.of(), unresolved,
                "the compiler prints these and `souther doc` has nothing to answer them with");
    }

    /** Every {@code E}-and-four-digits literal in every module's main sources. */
    private static Set<String> emittedCodes() throws IOException {
        Set<String> codes = new TreeSet<>();
        for (Path source : mainSources()) {
            Matcher m = CODE.matcher(Files.readString(source, StandardCharsets.UTF_8));
            while (m.find()) {
                codes.add(m.group(1));
            }
        }
        return codes;
    }

    /** Every module's main sources. The test runs in its own module directory, so the repo root is
     *  that directory's parent, and any module may emit a diagnostic. */
    private static List<Path> mainSources() throws IOException {
        Path module = Path.of("").toAbsolutePath();
        Path repo = Files.isDirectory(module.resolve(Path.of("src", "main", "java")))
                ? module.getParent() : module;
        List<Path> sources = new ArrayList<>();
        try (Stream<Path> modules = Files.list(repo)) {
            for (Path root : modules.map(m -> m.resolve(Path.of("src", "main", "java"))).toList()) {
                if (!Files.isDirectory(root)) {
                    continue;
                }
                try (Stream<Path> walk = Files.walk(root)) {
                    walk.filter(p -> p.toString().endsWith(".java")).forEach(sources::add);
                }
            }
        }
        return sources;
    }
}
