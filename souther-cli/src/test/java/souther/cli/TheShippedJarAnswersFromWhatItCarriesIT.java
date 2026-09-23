package souther.cli;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import souther.lsp.ToolingMetadata;

import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.zip.ZipEntry;
import java.util.zip.ZipFile;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The unit tests reach the doc commands directly and hand them class loaders they built. That
 * leaves the part only packaging decides untested: whether the specification and the doc sets
 * survive being shaded into one jar, and whether two jars' registries are merged rather than one
 * replacing the other. This runs the artifact that ships.
 */
class TheShippedJarAnswersFromWhatItCarriesIT {

    private static Path jar;

    @BeforeAll
    static void theBuiltJar() {
        jar = Path.of(System.getProperty("souther.jar", "target/souther.jar"));
        assertTrue(Files.isRegularFile(jar), "the shaded jar is built before this runs: " + jar.toAbsolutePath());
    }

    private record Answer(int code, String out, String err) {}

    private Answer souther(String... args) throws IOException, InterruptedException {
        List<String> command = new java.util.ArrayList<>(List.of(
                Path.of(System.getProperty("java.home"), "bin", "java").toString(), "-jar", jar.toString()));
        command.addAll(List.of(args));
        Process process = new ProcessBuilder(command).start();
        String out = new String(process.getInputStream().readAllBytes(), StandardCharsets.UTF_8);
        String err = new String(process.getErrorStream().readAllBytes(), StandardCharsets.UTF_8);
        return new Answer(process.waitFor(), out, err);
    }

    /**
     * The reading only a distribution can answer: the manifest is what carries the version, and the
     * unit tests run from class files, where there is none and the answer is {@code unreleased}.
     * Held against what the build says its version is, so a jar answering some other version — or
     * still answering as a build tree — is not a pass.
     */
    @Test
    void theShippedJarSaysWhichSoutherItIs() throws Exception {
        Answer answer = souther("--version");

        assertEquals(0, answer.code(), answer.err());
        assertEquals("souther " + System.getProperty("souther.version"), answer.out().strip());
    }

    /**
     * The tooling metadata survives the shade, and {@code souther tooling} prints the file the jar
     * carries: a client that reads it out of the archive and one that runs the command are told the
     * same thing.
     */
    @Test
    void theToolingCommandPrintsTheMetadataTheJarCarries() throws Exception {
        String carried;
        try (ZipFile archive = new ZipFile(jar.toFile())) {
            ZipEntry entry = archive.getEntry(ToolingMetadata.RESOURCE);
            assertNotNull(entry, "the shipped jar carries " + ToolingMetadata.RESOURCE);
            try (InputStream in = archive.getInputStream(entry)) {
                carried = new String(in.readAllBytes(), StandardCharsets.UTF_8);
            }
        }

        Answer answer = souther("tooling");

        assertEquals(0, answer.code(), answer.err());
        assertEquals(carried, answer.out());
    }

    @Test
    void theSpecificationIsAnsweredFromInsideTheJar() throws Exception {
        Answer answer = souther("doc", "purpose");

        assertEquals(0, answer.code(), answer.err());
        assertTrue(answer.out().contains("JVM-targeted language"), answer.out());
    }

    @Test
    void theCommandLinesOwnDocSetSurvivesTheShade() throws Exception {
        Answer answer = souther("doc");

        assertEquals(0, answer.code(), answer.err());
        List<String> names = answer.out().lines().map(l -> l.split("\t")[0]).toList();
        assertTrue(names.contains("cli/start-here"), "the shipped doc set is listed:\n" + answer.out());
        assertTrue(names.contains("cli/run"), "and so is every topic its index names");
    }

    @Test
    void aShippedTopicIsReadBackWhole() throws Exception {
        Answer answer = souther("doc", "cli/run");

        assertEquals(0, answer.code(), answer.err());
        assertTrue(answer.out().contains("--input"), answer.out());
    }

    @Test
    void everyDocSetOnTheClassPathIsRegistered() throws Exception {
        // Each contributing jar names its sets in a file at one path, so the shade has to append
        // them. If it replaced instead, whichever set lost would be missing here — which is the
        // whole reason both are asserted rather than one.
        Answer answer = souther("doc");

        List<String> sets = answer.out().lines()
                .map(l -> l.split("\t")[0])
                .filter(n -> n.contains("/"))
                .map(n -> n.substring(0, n.indexOf('/')))
                .distinct()
                .toList();
        assertTrue(sets.contains("cli"), "the sets found are " + sets);
        assertTrue(sets.contains("raoh"),
                "a dependency's own doc set survives the shade beside the tool's: " + sets);
    }

    @Test
    void aDependencysGuideIsReadFromTheVersionThisBuildDependsOn() throws Exception {
        Answer answer = souther("doc", "raoh/composition-patterns");

        assertEquals(0, answer.code(), answer.err());
        assertTrue(answer.out().contains("Composition Patterns"), answer.out());
    }

    @Test
    void theStandardLibraryIsAnsweredFromTheSameJar() throws Exception {
        Answer answer = souther("api", "Option");

        assertEquals(0, answer.code(), answer.err());
        assertTrue(answer.out().lines().anyMatch(l -> l.startsWith("Option.map(")), answer.out());
    }

    @Test
    void aBundledDependencysJavadocComesBackWithoutASourcesJarBesideTheArtifact() throws Exception {
        Answer answer = souther("japi", "net.unit8.raoh.Issue");

        assertEquals(0, answer.code(), answer.err());
        assertTrue(answer.out().contains("A single validation issue"),
                "the sources bundled into the jar answer for the dependency inside it:\n" + answer.out());
        assertTrue(answer.out().contains("of(net.unit8.raoh.Path path, String code, String message)"),
                "and name the parameters the class files do not carry:\n" + answer.out());
    }
}
