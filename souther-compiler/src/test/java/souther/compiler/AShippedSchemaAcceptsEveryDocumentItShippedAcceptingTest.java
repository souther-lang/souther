package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.report.AdequacyReport;
import souther.test.RepositoryLayout;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.io.IOException;
import java.io.InputStream;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A {@code schemaVersion} a release has shipped accepts every document it shipped accepting.
 *
 * <p>Which versions those are is a file each, beside this test: the schema as it was when a release
 * first shipped it, written by {@code bin/set-version.sh} when it sets a version that is not a
 * snapshot and kept as it was from then on. A version with no such file is open — nothing outside
 * this compiler has read a promise about it, and it may still be refined, a key made required
 * included. A version with one is frozen, and what is asked of it is asked against the copy that
 * shipped rather than against the last edit, so a narrowing cannot be made and then written down
 * as the new starting point.
 *
 * <p>And a build of a release is one whose schema has shipped. The script writes the copy; this is
 * what says it is there, for a release whose version was set some other way.
 */
class AShippedSchemaAcceptsEveryDocumentItShippedAcceptingTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /** Where the copies are, on the test classpath. */
    private static final String SHIPPED = "/souther/compiler/schema/released/";

    private static final Pattern A_COPY = Pattern.compile("adequacy-schema-(\\d+)\\.json");

    /** Every version a release shipped is accepted by its schema as it is now. */
    @Test
    void everyShippedVersionStillAcceptsWhatItShippedAccepting() {
        List<Integer> shipped = shippedVersions();
        assertFalse(shipped.isEmpty(), "no shipped schema was found, so nothing was asked");

        List<String> narrowed = new ArrayList<>();
        for (int version : shipped) {
            JsonNode current = read("/souther/adequacy-schema-" + version + ".json");
            assertNotNull(current, "the schema of a shipped version is still shipped: " + version);
            SchemaEvolution.narrowings(read(SHIPPED + "adequacy-schema-" + version + ".json"),
                            current)
                    .forEach(each -> narrowed.add(version + " " + each));
        }
        assertEquals(List.of(), narrowed,
                "a shipped schemaVersion accepts fewer documents than it shipped accepting;"
                        + " a narrowing raises the version instead");
    }

    /** A build of a release writes documents of a version a release has shipped. */
    @Test
    void aReleaseWritesASchemaThatHasShipped() {
        String version = theCompilersVersion();
        if (freezesTheSchema(version)) {
            assertTrue(shippedVersions().contains(AdequacyReport.SCHEMA_VERSION),
                    () -> version + " is a release and writes schemaVersion "
                            + AdequacyReport.SCHEMA_VERSION + ", and no copy of that schema as it"
                            + " shipped is kept; bin/set-version.sh writes it");
        }
    }

    /**
     * Which versions freeze the schema: every one that is not a snapshot.
     *
     * <p>A candidate as well as a final release. What it ships is read by whoever downloaded it, and
     * the page it is listed on calling it a prerelease does not make the promise any less made.
     */
    @Test
    void everyVersionThatIsNotASnapshotFreezesTheSchema() {
        assertTrue(freezesTheSchema("0.4.0"));
        assertTrue(freezesTheSchema("0.4.0-rc1"));
        assertFalse(freezesTheSchema("0.4.1-SNAPSHOT"));
    }

    /** The same rule {@code bin/set-version.sh} copies the schema by. */
    private static boolean freezesTheSchema(String version) {
        return !version.endsWith("-SNAPSHOT");
    }

    /** The version this compiler is built at, as its own pom says. */
    private static String theCompilersVersion() {
        for (String built : RepositoryLayout.ofWorkingDirectory().coordinatesBuilt()) {
            String[] parts = built.split(":");
            if (parts[1].equals("souther-compiler")) {
                return parts[2];
            }
        }
        throw new AssertionError("the reactor builds no souther-compiler");
    }

    private static List<Integer> shippedVersions() {
        URL at = AShippedSchemaAcceptsEveryDocumentItShippedAcceptingTest.class.getResource(SHIPPED);
        assertNotNull(at, SHIPPED + " is on the test classpath");
        List<Integer> out = new ArrayList<>();
        try (Stream<Path> files = Files.list(Path.of(at.toURI()))) {
            files.forEach(file -> {
                Matcher named = A_COPY.matcher(file.getFileName().toString());
                assertTrue(named.matches(), () -> "not a shipped schema: " + file);
                out.add(Integer.parseInt(named.group(1)));
            });
        } catch (IOException | URISyntaxException e) {
            throw new AssertionError(e);
        }
        out.sort(null);
        return out;
    }

    private static JsonNode read(String resource) {
        try (InputStream in = AShippedSchemaAcceptsEveryDocumentItShippedAcceptingTest.class
                .getResourceAsStream(resource)) {
            return in == null ? null
                    : JSON.readTree(new String(in.readAllBytes(), StandardCharsets.UTF_8));
        } catch (IOException e) {
            throw new AssertionError(e);
        }
    }
}
