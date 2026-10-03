package souther.architecture;

import org.junit.jupiter.api.Test;
import souther.test.RepositoryLayout;

import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a publication may depend on as a snapshot is what this reactor builds, and nothing else.
 *
 * <p>The {@code snapshot} profile refuses a snapshot dependency, because the publication is a second
 * build of the commit CI checked and a snapshot can resolve to something else between the two. Its
 * own modules are snapshots there and are built in the same invocation, so they are exempt — and the
 * exemption is the set the reactor builds, which no pattern over a coordinate says: the group holds
 * artifacts released from elsewhere, souther-build-api among them, which the profile has to go on
 * refusing as snapshots. So the modules are named one at a time, and this holds the names to the
 * modules the root pom builds, both ways: one added to the reactor and not exempted fails every
 * publication, and one exempted that the reactor does not build is a dependency nothing checks.
 *
 * <p>A release builds every module at the release version, so the {@code release} profile exempts
 * nothing.
 */
class TheSnapshotProfileExemptsExactlyTheReactorTest {

    private static final RepositoryLayout REPOSITORY = RepositoryLayout.ofWorkingDirectory();

    private static final String[] EXCLUDES = {"build", "plugins", "plugin", "executions", "execution",
            "configuration", "rules", "requireReleaseDeps", "excludes", "exclude"};

    @Test
    void theSnapshotProfileExemptsTheModulesTheReactorBuilds() {
        Set<String> built = new TreeSet<>();
        for (String artifactId : REPOSITORY.artifactIdsBuilt()) {
            built.add("org.souther-lang:" + artifactId);
        }
        assertEquals(built, new TreeSet<>(REPOSITORY.rootProfileTexts("snapshot", EXCLUDES)));
    }

    @Test
    void theReleaseProfileExemptsNothing() {
        assertEquals(List.of(), REPOSITORY.rootProfileTexts("release", EXCLUDES));
    }
}
