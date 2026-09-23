package souther.lsp;

import org.junit.jupiter.api.Test;
import souther.test.RepositoryLayout;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.io.InputStream;
import java.lang.management.ManagementFactory;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The tooling metadata says what the build did, and each thing it says is held against the thing it
 * describes rather than against another copy of the same words.
 *
 * <p>The Java it names is read off a class this module was compiled to, because a client that
 * starts the server on less is refused by the class file and not by the pom. The JVM arguments are
 * read off this test's own JVM, which the build starts with the arguments it gives every launcher,
 * and against the root pom's property, which is where both come from. The contracts it names are
 * looked for where it says they are.
 */
class TheToolingMetadataStatesWhatThisBuildDidTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    @Test
    void everyPropertyWasFilledIn() {
        String text = ToolingMetadata.text();

        assertFalse(text.contains("${"), "a property the build did not fill in: " + text);
    }

    @Test
    void theJavaItNamesIsTheOneTheseClassesNeed() throws Exception {
        int major;
        try (InputStream in = ToolingMetadata.class.getResourceAsStream("ToolingMetadata.class")) {
            assertNotNull(in);
            byte[] head = in.readNBytes(8);
            major = ((head[6] & 0xFF) << 8) | (head[7] & 0xFF);
        }

        assertEquals(major - 44, metadata().get("runtime").get("java").get("minimumFeature").asInt(),
                "these classes are class file version " + major + ", which is Java " + (major - 44));
        assertEquals(Integer.toString(major - 44), rootPomProperty("souther.java.minimum"));
    }

    @Test
    void theJvmArgumentsAreTheStackTheBuildGives() {
        List<String> stated = new ArrayList<>();
        for (JsonNode argument : metadata().get("runtime").get("java").get("requiredJvmArgs")) {
            stated.add(argument.asString());
        }

        assertEquals(List.of("-Xss" + rootPomProperty("souther.jvm.stack")), stated);
        List<String> given = ManagementFactory.getRuntimeMXBean().getInputArguments();
        assertTrue(given.containsAll(stated),
                "the tests run on what a client is told to give the JVM: " + given);
    }

    @Test
    void theContractsItNamesAreWhereItSaysTheyAre() {
        JsonNode contracts = metadata().get("contracts");
        String syntax = contracts.get("syntax").get("resource").asString();
        String options = contracts.get("lspInitializationOptions").get("resource").asString();

        ClassLoader loader = ToolingMetadata.class.getClassLoader();
        assertNotNull(loader.getResource(syntax + "grammar.ebnf"), syntax);
        assertNotNull(loader.getResource(options), options);
        int version = contracts.get("lspInitializationOptions").get("schemaVersion").asInt();
        assertTrue(options.endsWith("-" + version + ".schema.json"),
                "a schema's file is named by the version it is: " + options);
    }

    private static JsonNode metadata() {
        return JSON.readTree(ToolingMetadata.text());
    }

    private static String rootPomProperty(String name) {
        return RepositoryLayout.ofWorkingDirectory().rootProperty(name);
    }
}
