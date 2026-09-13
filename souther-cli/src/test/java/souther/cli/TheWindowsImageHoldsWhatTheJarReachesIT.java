package souther.cli;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import souther.test.RepositoryLayout;

import java.io.PrintWriter;
import java.io.StringWriter;
import java.lang.module.ModuleDescriptor;
import java.lang.module.ModuleFinder;
import java.lang.module.ModuleReference;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.LinkedHashSet;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.spi.ToolProvider;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The Windows distribution that carries a runtime carries the modules the packaging script names,
 * and a module left out of that list is missing from the image rather than from the build: the
 * command that needs it answers with a class it cannot find, and every other command answers as if
 * the image were complete. So the list is held against what the jar actually reaches, which is what
 * jdeps answers, and a dependency added without a look at the packaging script is refused here.
 *
 * <p>The list is a constant in the script rather than something the script computes, because
 * {@code jdeps --print-module-deps} answers a narrower question than this one: asked to ignore what
 * it cannot resolve, it drops the modules reached only from a class that also reaches something
 * missing, and the jar reaches an annotation library it does not carry. What is checked here is
 * therefore containment, in the direction that matters — the image may hold a module the jar no
 * longer reaches, and may not be short of one it does.
 */
class TheWindowsImageHoldsWhatTheJarReachesIT {

    private static final Pattern DECLARED = Pattern.compile("\\$modules\\s*=\\s*'([^']+)'");
    private static final Pattern REACHED = Pattern.compile("->\\s*(\\S+)");

    private static Path jar;
    private static Path script;

    @BeforeAll
    static void theBuiltJarAndTheScriptThatPackagesIt() {
        jar = Path.of(System.getProperty("souther.jar", "target/souther.jar"));
        assertTrue(Files.isRegularFile(jar),
                "the shaded jar is built before this runs: " + jar.toAbsolutePath());
        script = RepositoryLayout.ofWorkingDirectory().root().resolve("bin/package-windows.ps1");
        assertTrue(Files.isRegularFile(script), "the packaging script is at " + script);
    }

    @Test
    void theModulesTheScriptNamesCoverEveryModuleTheJarReaches() throws Exception {
        Set<String> declared = declaredModules();
        Set<String> reached = modulesTheJarReaches();

        // A reading that found nothing would agree with any list at all, so the run says how much it
        // read before it says the two agree.
        assertFalse(reached.isEmpty(), "jdeps named no module the jar reaches, so nothing was held"
                + " against the script's list");

        Set<String> missing = new LinkedHashSet<>(reached);
        missing.removeAll(declared);
        assertTrue(missing.isEmpty(), "the jar reaches " + missing + ", which "
                + script.getFileName() + " does not name: the image would be built without them and"
                + " only the command that needs one would say so. It names " + declared);
    }

    private static Set<String> declaredModules() throws Exception {
        Matcher said = DECLARED.matcher(Files.readString(script));
        assertTrue(said.find(), "no `$modules = '...'` in " + script);
        return Stream.of(said.group(1).split(","))
                .map(String::trim)
                .filter(module -> !module.isEmpty())
                .collect(Collectors.toCollection(LinkedHashSet::new));
    }

    /**
     * The system modules jdeps names as the jar's, taken from the summary rather than from the
     * module-path answer. A target that is not the name of a module in this JDK is not one: that is
     * how the jar itself, and the line jdeps writes for a dependency it could not resolve, are left
     * out without reading either against wording that changes with the locale it ran under.
     */
    private static Set<String> modulesTheJarReaches() {
        ToolProvider jdeps = ToolProvider.findFirst("jdeps")
                .orElseThrow(() -> new IllegalStateException("this JDK carries no jdeps"));
        StringWriter said = new StringWriter();
        StringWriter complained = new StringWriter();
        int ended = jdeps.run(new PrintWriter(said), new PrintWriter(complained),
                "-s", "--multi-release", "25", jar.toString());
        assertTrue(ended == 0, "jdeps ended with " + ended + ": " + complained);

        Set<String> system = ModuleFinder.ofSystem().findAll().stream()
                .map(ModuleReference::descriptor)
                .map(ModuleDescriptor::name)
                .collect(Collectors.toSet());
        Set<String> reached = new LinkedHashSet<>();
        for (String line : said.toString().split("\\R")) {
            Matcher target = REACHED.matcher(line);
            if (target.find() && system.contains(target.group(1))) {
                reached.add(target.group(1));
            }
        }
        return reached;
    }
}
