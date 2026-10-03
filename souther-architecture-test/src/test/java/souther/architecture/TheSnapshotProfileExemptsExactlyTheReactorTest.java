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
 * build of the commit CI checked and a snapshot can resolve to something else between the two. What
 * the reactor builds is a snapshot there and is built in the same invocation, so it is exempt — and
 * the exemption is the artifacts the reactor builds, whole coordinates and not a pattern over them.
 * The group holds artifacts released from elsewhere, souther-build-api among them, and a module of
 * this reactor at another version is one it does not build; both are resolved from a repository and
 * have to go on being refused. So each module is named with its version, and this holds the names to
 * what the root pom's modules build, both ways: one added to the reactor and not exempted fails
 * every publication, and one exempted that the reactor does not build is a dependency nothing
 * checks.
 *
 * <p>The version is written {@code ${project.version}}, which each module the rule runs in reads as
 * its own, so it is asked here as every module the reactor builds would read it.
 *
 * <p>A release builds every module at the release version, so the {@code release} profile exempts
 * nothing. That is asked at the same place the snapshot profile's exemptions are read, which the
 * first test shows is where they are.
 */
class TheSnapshotProfileExemptsExactlyTheReactorTest {

    private static final RepositoryLayout REPOSITORY = RepositoryLayout.ofWorkingDirectory();

    private static final String[] EXCLUDES = {"build", "plugins", "plugin", "executions", "execution",
            "configuration", "rules", "requireReleaseDeps", "excludes", "exclude"};

    @Test
    void theSnapshotProfileExemptsWhatTheReactorBuilds() {
        List<String> built = REPOSITORY.coordinatesBuilt();
        List<String> written = REPOSITORY.rootProfileTexts("snapshot", EXCLUDES);
        for (String coordinate : built) {
            String version = coordinate.substring(coordinate.lastIndexOf(':') + 1);
            Set<String> asRead = new TreeSet<>();
            for (String exclude : written) {
                asRead.add(exclude.replace("${project.version}", version));
            }
            assertEquals(new TreeSet<>(built), asRead, "as the module building " + coordinate + " reads them");
        }
    }

    @Test
    void theReleaseProfileExemptsNothing() {
        assertEquals(List.of(), REPOSITORY.rootProfileTexts("release", EXCLUDES));
    }
}
