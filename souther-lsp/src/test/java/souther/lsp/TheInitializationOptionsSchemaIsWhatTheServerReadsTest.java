package souther.lsp;

import org.junit.jupiter.api.Test;
import souther.compiler.query.Adequacy;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;
import tools.jackson.databind.node.JsonNodeFactory;
import tools.jackson.databind.node.ObjectNode;

import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The schema a client reads before it starts the server describes what the server then does with
 * the options.
 *
 * <p>The schema is what a client is held to, so each side of it is read from the schema file the
 * tooling metadata names and held against the server's own tables: the members against
 * {@link SoutherExtension}, and the values of a member against what {@link SoutherInitializationOptions}
 * accepts for it. A value the schema allows and the server reads as absent, or one the server reads
 * and the schema forbids, is a client told one thing and served another.
 */
class TheInitializationOptionsSchemaIsWhatTheServerReadsTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /** As sets: the order of an object's members says nothing in JSON, so it is not held here. */
    @Test
    void theMembersTheSchemaNamesAreTheOnesTheServerAdvertises() {
        Set<String> named = new HashSet<>();
        schema().get("properties").propertyNames().forEach(named::add);

        assertEquals(SoutherExtension.advertised().keySet(), named);
    }

    /**
     * Every member the server advertises is one it reads and checks: a value its schema does not
     * allow comes back as unread under that member's name. Advertising a member is not evidence of
     * this, since the advertisement and the expectation above are both drawn from the same table.
     */
    @Test
    void everyAdvertisedMemberIsReadAndItsValueChecked() {
        for (SoutherExtension extension : SoutherExtension.values()) {
            for (JsonNode written : List.<JsonNode>of(JSON.valueToTree(notAllowedFor(extension)),
                    JsonNodeFactory.instance.nullNode())) {
                ObjectNode souther = JSON.createObjectNode();
                souther.set(extension.member(), written);
                ObjectNode options = JSON.createObjectNode();
                options.set("souther", souther);

                SoutherInitializationOptions read = SoutherInitializationOptions.decode(options);

                assertEquals(1, read.unread().size(), extension + " " + written + ": " + read);
                assertTrue(read.unread().getFirst().contains("souther." + extension.member() + " "),
                        read.unread().getFirst());
            }
        }
    }

    /** A value no schema for the member allows. A switch with no default, so a member added to the
     * table is a test that does not compile until it says how that member is misused. */
    private static Object notAllowedFor(SoutherExtension extension) {
        return switch (extension) {
            case ADEQUACY -> 42;
        };
    }

    @Test
    void everyAdequacyTheSchemaAllowsIsReadAsTheLevelItNames() {
        JsonNode adequacy = schema().get("properties").get("adequacy");
        List<String> allowed = new ArrayList<>();
        for (JsonNode value : adequacy.get("enum")) {
            allowed.add(value.asString());
        }
        List<String> spelt = new ArrayList<>();
        for (Adequacy.Level level : Adequacy.Level.values()) {
            spelt.add(level.spelling());
        }

        assertEquals(spelt, allowed);
        for (Adequacy.Level level : Adequacy.Level.values()) {
            assertEquals(new SoutherInitializationOptions(level, List.of()),
                    decode(Map.of("souther", Map.of("adequacy", level.spelling()))));
        }
        assertEquals(Adequacy.Level.OFF.spelling(), adequacy.get("default").asString());
        assertEquals(SoutherInitializationOptions.NONE, decode(Map.of("souther", Map.of())));
    }

    /** A member the schema does not name is a later server's, and nothing is said about it. */
    @Test
    void aMemberTheSchemaDoesNotNameIsIgnoredWithoutAWord() {
        assertEquals(SoutherInitializationOptions.NONE,
                decode(Map.of("souther", Map.of("aLaterFeature", Map.of("on", true)))));
        assertEquals(SoutherInitializationOptions.NONE, decode(Map.of("anotherServer", 1)));
    }

    @Test
    void aValueTheSchemaDoesNotAllowIsReadAsAbsentAndSaidSo() {
        for (Object written : List.of("witnes", "WITNESS", 42, true, List.of("all"))) {
            SoutherInitializationOptions read =
                    decode(Map.of("souther", Map.of("adequacy", written)));

            assertEquals(Adequacy.Level.OFF, read.adequacy(), written.toString());
            assertEquals(1, read.unread().size(), read.unread().toString());
            assertTrue(read.unread().getFirst().contains("adequacy"), read.unread().getFirst());
        }
    }

    /** JSON {@code null} is written, and is not an object; only a member that is not there is absent. */
    @Test
    void aSoutherMemberThatIsNotAnObjectIsSaidToBeUnread() {
        for (JsonNode written : List.<JsonNode>of(JSON.valueToTree("witness"),
                JsonNodeFactory.instance.nullNode())) {
            ObjectNode options = JSON.createObjectNode();
            options.set("souther", written);

            SoutherInitializationOptions read = SoutherInitializationOptions.decode(options);

            assertEquals(Adequacy.Level.OFF, read.adequacy());
            assertEquals(1, read.unread().size(), written + ": " + read.unread());
        }
    }

    private static SoutherInitializationOptions decode(Object initializationOptions) {
        return SoutherInitializationOptions.decode(JSON.valueToTree(initializationOptions));
    }

    private static JsonNode schema() {
        String resource = JSON.readTree(ToolingMetadata.text())
                .get("contracts").get("lspInitializationOptions").get("resource").asString();
        try (InputStream in = ToolingMetadata.class.getClassLoader().getResourceAsStream(resource)) {
            assertNotNull(in, resource);
            return JSON.readTree(in);
        } catch (IOException e) {
            throw new AssertionError(resource, e);
        }
    }
}
