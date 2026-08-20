package souther.cli.init;

import java.util.Set;

/**
 * The build plugins a generated project declares, and the build protocol they were released
 * speaking.
 *
 * <p>Written down here because there is nowhere to read it from. A plugin is released from its own
 * repository on its own version series (#137), so the compiler running this command knows its own
 * version and cannot know the plugin's — and a build file has to name one, since a Maven plugin
 * without a version resolves to whatever is newest and a Gradle {@code plugins} block will not take
 * a declaration without one.
 *
 * <p>What can rot is caught by the number beside it. The plugin drives a Souther over a numbered
 * protocol, and this compiler's own driver states which number it speaks; a release that moves the
 * protocol without these versions moving with it would have {@code init} writing a project whose
 * plugin cannot drive the Souther it names. {@link #PROTOCOLS} is what those releases speak, and a
 * test holds it against the driver in this build.
 */
final class BuildPlugins {

    private BuildPlugins() {}

    /** The group both plugins and the runtime are published under. */
    static final String GROUP = "org.souther-lang";

    static final String MAVEN_ARTIFACT = "souther-maven-plugin";

    static final String MAVEN_VERSION = "0.1.0";

    /** How Gradle names the plugin, which is not the artifact it resolves. */
    static final String GRADLE_ID = "org.souther-lang.souther";

    static final String GRADLE_VERSION = "0.1.0";

    /** The runtime the generated code calls, at the version of the Souther that generated it. */
    static final String RUNTIME_ARTIFACT = "souther-runtime";

    /** The build protocols the releases named above speak. */
    static final Set<Integer> PROTOCOLS = Set.of(1);
}
