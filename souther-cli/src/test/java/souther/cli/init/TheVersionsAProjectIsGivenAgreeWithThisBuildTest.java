package souther.cli.init;

import org.junit.jupiter.api.Test;
import souther.compiler.Compiler;
import souther.compiler.meta.ModulePath;
import souther.compiler.diag.Located;
import souther.compiler.query.Adequacy;

import java.io.InputStream;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The numbers a generated project is given are ones this build can still stand behind.
 *
 * <p>A build file this command writes pins the world as it was when this compiler was released, and
 * the pins it cannot read from anywhere — the build plugins are released from their own
 * repositories, on their own version series — are written down in {@link BuildPlugins}. What catches
 * a pin that has gone stale is the number beside it: a plugin drives a Souther over a numbered
 * protocol, and this build states which number it speaks.
 */
class TheVersionsAProjectIsGivenAgreeWithThisBuildTest {

    /** Where a driver states the build protocol it was built against, for a plugin to read. */
    private static final String PROTOCOL = "META-INF/souther-build-protocol";

    /**
     * The plugins {@code init} writes speak the protocol this Souther's driver states.
     *
     * <p>Fails the day the protocol moves without those versions moving with it, which is the day a
     * project this command writes would stop being drivable by the plugin it names — reported as a
     * red build here rather than as a refusal in somebody's first build.
     */
    @Test
    void thePinnedPluginsSpeakTheProtocolThisDriverStates() throws Exception {
        List<URL> stated = Collections.list(
                getClass().getClassLoader().getResources(PROTOCOL));
        assertEquals(1, stated.size(),
                "the build protocol is stated " + stated.size() + " times on this class path");
        String protocol;
        try (InputStream in = stated.get(0).openStream()) {
            protocol = new String(in.readAllBytes(), StandardCharsets.UTF_8).trim();
        }

        assertTrue(BuildPlugins.PROTOCOLS.contains(Integer.valueOf(protocol)),
                "this Souther speaks build protocol " + protocol + ", and `souther init` writes "
                        + "souther-maven-plugin " + BuildPlugins.MAVEN_VERSION + " and "
                        + "souther-gradle-plugin " + BuildPlugins.GRADLE_VERSION + ", which speak "
                        + BuildPlugins.PROTOCOLS + ". Release the plugins against this protocol and "
                        + "write their versions into BuildPlugins.");
    }

    /**
     * A generated project reads its own classes with the release this compiler emits.
     *
     * <p>Read off a class this compiler actually produced rather than off its source: what a
     * generated project has to be able to load is the class file, and the number in the pom is the
     * claim about it.
     */
    @Test
    void theJavaReleaseAProjectDeclaresIsTheOneTheCompilerEmits() {
        List<Located> warnings = new ArrayList<>();
        Map<String, byte[]> classes = Compiler.compiledModules(
                List.of("module probe\n\ndata Amount = Int\n    invariant value >= 0\n"),
                ModulePath.EMPTY, warnings, Adequacy.Asked.NOTHING).classes();
        byte[] emitted = classes.values().iterator().next();
        assertNotNull(emitted);

        int major = ((emitted[6] & 0xFF) << 8) | (emitted[7] & 0xFF);

        assertEquals(major - 44, Integer.parseInt(Templates.javaRelease()),
                "this compiler emits class file version " + major + " (Java " + (major - 44)
                        + ") and `souther init` writes maven.compiler.release "
                        + Templates.javaRelease());
    }
}
