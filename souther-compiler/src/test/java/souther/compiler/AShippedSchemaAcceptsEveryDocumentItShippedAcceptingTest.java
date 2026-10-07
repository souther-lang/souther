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
import java.util.Comparator;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A {@code schemaVersion} a release has shipped accepts every document any release shipped it
 * accepting.
 *
 * <p>What each release shipped is a file beside this test, under a directory named for the release:
 * the schema as that release carried it, written by {@code bin/set-version.sh} when it sets the
 * release's version and never written again. A version no release has shipped is open — nothing
 * outside this compiler has read a promise about it, and it may still be refined, a key made
 * required included. A version some release shipped is frozen, and is held to every release that
 * shipped it rather than to one: a key the second release of a version added is a key documents of
 * that version now carry, and taking it out is as much a narrowing as taking out one the first
 * release had. Held to the copies rather than to the last edit, so a narrowing cannot be made and
 * then written down as the new starting point.
 *
 * <p>And a build of a release is one whose schema is recorded as it ships. The script writes the
 * copy; this is what says it is there, and that it is what this build ships, for a release whose
 * version was set some other way.
 */
class AShippedSchemaAcceptsEveryDocumentItShippedAcceptingTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /** Where the copies are, on the test classpath: one directory per release. */
    private static final String SHIPPED = "/souther/compiler/schema/released/";

    private static final Pattern A_COPY = Pattern.compile("adequacy-schema-(\\d+)\\.json");

    /** What one release shipped: the release, the version of the schema it wrote, and where the
     *  copy is on the classpath. */
    private record Shipped(String release, int schemaVersion, String resource) {}

    /** Every version a release shipped is accepted by its schema as it is now. */
    @Test
    void everyShippedVersionStillAcceptsWhatEveryReleaseOfItAccepted() {
        List<Shipped> shipped = shipped();
        assertFalse(shipped.isEmpty(), "no shipped schema was found, so nothing was asked");

        List<String> narrowed = new ArrayList<>();
        for (Shipped each : shipped) {
            JsonNode current = read("/souther/adequacy-schema-" + each.schemaVersion() + ".json");
            assertNotNull(current,
                    () -> "the schema of a shipped version is still shipped: " + each);
            SchemaEvolution.narrowings(read(each.resource()), current)
                    .forEach(at -> narrowed.add(each.release() + " (schemaVersion "
                            + each.schemaVersion() + ") " + at));
        }
        assertEquals(List.of(), narrowed,
                "a shipped schemaVersion accepts fewer documents than a release shipped it"
                        + " accepting; a narrowing raises the version instead");
    }

    /** A build of a release has a copy of the schema it writes, and the copy is that schema. */
    @Test
    void aReleaseRecordsTheSchemaItShips() {
        String version = theCompilersVersion();
        if (freezesTheSchema(version)) {
            assertEquals(List.of(), unrecorded(version, AdequacyReport.SCHEMA_VERSION));
        }
    }

    /**
     * The same question put to releases whose answers are known, since a build of this checkout is
     * a snapshot and never asks it.
     *
     * <p>The first candidate shipped schema 1 and the compiler carries it as it was. Version 23 has
     * gained words since the release that shipped it, so what this checkout would ship under that
     * release's name is not what it shipped. And a release nobody cut has no copy.
     */
    @Test
    void aReleaseIsHeldToTheCopyOfWhatItShips() {
        assertEquals(List.of(), unrecorded("0.1.0-rc4", 1));
        assertEquals(List.of("0.3.0 ships a schema other than the copy kept of it"),
                unrecorded("0.3.0", 23));
        assertEquals(List.of("9.9.9 is a release and no copy of the schema it ships is kept;"
                        + " bin/set-version.sh writes it"),
                unrecorded("9.9.9", 23));
    }

    /** What is wrong with the copy kept of what {@code release} ships as {@code schemaVersion}. */
    private static List<String> unrecorded(String release, int schemaVersion) {
        Shipped recorded = shipped().stream()
                .filter(each -> each.release().equals(release))
                .findFirst()
                .orElse(null);
        if (recorded == null) {
            return List.of(release + " is a release and no copy of the schema it ships is kept;"
                    + " bin/set-version.sh writes it");
        }
        if (recorded.schemaVersion() != schemaVersion) {
            return List.of(release + " writes schemaVersion " + schemaVersion
                    + " and its copy is of " + recorded.schemaVersion());
        }
        if (!text("/souther/adequacy-schema-" + schemaVersion + ".json")
                .equals(text(recorded.resource()))) {
            return List.of(release + " ships a schema other than the copy kept of it");
        }
        return List.of();
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

    /**
     * Every release's copy, by the schemaVersion it shipped and then by the release's name.
     *
     * <p>A directory per release holding one schema, and nothing else: a second file under one
     * release would be a second answer to what it shipped, and a directory named for a snapshot is
     * a copy of something that never shipped.
     */
    private static List<Shipped> shipped() {
        URL at = AShippedSchemaAcceptsEveryDocumentItShippedAcceptingTest.class.getResource(SHIPPED);
        assertNotNull(at, SHIPPED + " is on the test classpath");
        List<Shipped> out = new ArrayList<>();
        try (Stream<Path> releases = Files.list(Path.of(at.toURI()))) {
            for (Path release : releases.toList()) {
                String name = release.getFileName().toString();
                assertTrue(Files.isDirectory(release) && freezesTheSchema(name),
                        () -> "not a release: " + release);
                try (Stream<Path> files = Files.list(release)) {
                    List<Path> copies = files.toList();
                    assertEquals(1, copies.size(),
                            () -> "a release ships one schema, and " + release + " holds " + copies);
                    Matcher named = A_COPY.matcher(copies.get(0).getFileName().toString());
                    assertTrue(named.matches(), () -> "not a shipped schema: " + copies.get(0));
                    out.add(new Shipped(name, Integer.parseInt(named.group(1)),
                            SHIPPED + name + "/" + copies.get(0).getFileName()));
                }
            }
        } catch (IOException | URISyntaxException e) {
            throw new AssertionError(e);
        }
        out.sort(Comparator.comparingInt(Shipped::schemaVersion).thenComparing(Shipped::release));
        return out;
    }

    private static JsonNode read(String resource) {
        String text = text(resource);
        return text == null ? null : JSON.readTree(text);
    }

    private static String text(String resource) {
        try (InputStream in = AShippedSchemaAcceptsEveryDocumentItShippedAcceptingTest.class
                .getResourceAsStream(resource)) {
            return in == null ? null : new String(in.readAllBytes(), StandardCharsets.UTF_8);
        } catch (IOException e) {
            throw new AssertionError(e);
        }
    }
}
