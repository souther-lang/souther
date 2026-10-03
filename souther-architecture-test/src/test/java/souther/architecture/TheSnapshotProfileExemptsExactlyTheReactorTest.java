package souther.architecture;

import org.apache.maven.artifact.Artifact;
import org.apache.maven.artifact.DefaultArtifact;
import org.apache.maven.artifact.handler.ArtifactHandler;
import org.apache.maven.enforcer.rules.utils.ArtifactUtils;
import org.junit.jupiter.api.Test;
import souther.test.RepositoryLayout;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a publication may depend on as a snapshot is what this reactor builds, and nothing else.
 *
 * <p>The {@code snapshot} profile refuses a snapshot dependency, because the publication is a second
 * build of the commit CI checked and a snapshot can resolve to something else between the two. What
 * the reactor builds is a snapshot there and is built in the same invocation, so it is exempt — and
 * the exemption is exactly the artifacts the reactor builds. The group holds artifacts released
 * from elsewhere, souther-build-api among them, and a module of this reactor at any other version is
 * one it does not build; both are resolved from a repository and have to go on being refused.
 *
 * <p>Asked of the Enforcer's own matcher, at the version the profile runs, and not of how the
 * exemptions are spelled. What a pattern matches is the matcher's to say — a bare version in one is
 * that version or any later — so a check comparing spellings holds the profile to a reading of the
 * matcher rather than to the matcher.
 *
 * <p>The version in an exemption is written {@code ${project.version}}, which each module the rule
 * runs in reads as its own, so every question is asked as each module the reactor builds would ask
 * it.
 *
 * <p>A release builds every module at the release version, so the {@code release} profile exempts
 * nothing. That is read at the same place the snapshot profile's exemptions are, which the tests
 * before it show is where they are.
 */
class TheSnapshotProfileExemptsExactlyTheReactorTest {

    private static final RepositoryLayout REPOSITORY = RepositoryLayout.ofWorkingDirectory();

    private static final String[] EXCLUDES = {"build", "plugins", "plugin", "executions", "execution",
            "configuration", "rules", "requireReleaseDeps", "excludes", "exclude"};

    private static final List<String> BUILT = REPOSITORY.coordinatesBuilt();

    @Test
    void everythingTheReactorBuildsIsExempt() {
        for (String reading : BUILT) {
            List<String> exemptions = asReadBy(reading);
            for (String built : BUILT) {
                assertTrue(exempts(exemptions, built), built + ", as " + reading + " reads them");
            }
        }
    }

    @Test
    void nothingTheReactorDoesNotBuildIsExempt() {
        for (String reading : BUILT) {
            List<String> exemptions = asReadBy(reading);
            for (String built : BUILT) {
                for (String other : notBuiltBeside(built)) {
                    assertFalse(exempts(exemptions, other), other + ", as " + reading + " reads them");
                }
            }
        }
    }

    @Test
    void eachExemptionIsOneArtifactTheReactorBuilds() {
        for (String reading : BUILT) {
            for (String exemption : asReadBy(reading)) {
                List<String> matched = new ArrayList<>();
                for (String built : BUILT) {
                    if (exempts(List.of(exemption), built)) {
                        matched.add(built);
                    }
                }
                assertEquals(1, matched.size(), exemption + " matches " + matched);
            }
        }
    }

    @Test
    void theReleaseProfileExemptsNothing() {
        assertEquals(List.of(), REPOSITORY.rootProfileTexts("release", EXCLUDES));
    }

    /** The snapshot profile's exemptions as the module building {@code coordinate} reads them. */
    private static List<String> asReadBy(String coordinate) {
        String version = partOf(coordinate, 2);
        List<String> out = new ArrayList<>();
        for (String written : REPOSITORY.rootProfileTexts("snapshot", EXCLUDES)) {
            out.add(written.replace("${project.version}", version));
        }
        return out;
    }

    /**
     * Coordinates beside {@code built} that the reactor does not build: the same artifact at a
     * version below it, above it and released, and an artifact of the same group it does not build
     * at the same version.
     */
    private static List<String> notBuiltBeside(String built) {
        String group = partOf(built, 0);
        String artifact = partOf(built, 1);
        String version = partOf(built, 2);
        return List.of(
                group + ":" + artifact + ":0-SNAPSHOT",
                group + ":" + artifact + ":999999-SNAPSHOT",
                group + ":" + artifact + ":" + version.replace("-SNAPSHOT", ""),
                group + ":souther-build-api:" + version);
    }

    /** Whether the rule exempts {@code coordinate}, asked the way the rule asks it. */
    private static boolean exempts(List<String> exemptions, String coordinate) {
        Artifact artifact = new DefaultArtifact(partOf(coordinate, 0), partOf(coordinate, 1),
                partOf(coordinate, 2), Artifact.SCOPE_COMPILE, "jar", null, new Jar());
        return ArtifactUtils.matchDependencyArtifact(artifact, exemptions);
    }

    /** What Maven's handler for a jar answers. Its own class is in maven-core, which nothing here
     *  needs otherwise. */
    private static final class Jar implements ArtifactHandler {
        @Override
        public String getExtension() {
            return "jar";
        }

        @Override
        public String getDirectory() {
            return null;
        }

        @Override
        public String getClassifier() {
            return null;
        }

        @Override
        public String getPackaging() {
            return "jar";
        }

        @Override
        public boolean isIncludesDependencies() {
            return false;
        }

        @Override
        public String getLanguage() {
            return "java";
        }

        @Override
        public boolean isAddedToClasspath() {
            return true;
        }
    }

    private static String partOf(String coordinate, int index) {
        return coordinate.split(":")[index];
    }
}
