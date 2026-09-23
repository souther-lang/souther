package souther.lsp;

import org.junit.jupiter.api.Test;
import souther.compiler.query.Adequacy;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

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

    @Test
    void theMembersTheSchemaNamesAreTheOnesTheServerAdvertises() {
        List<String> named = new ArrayList<>();
        schema().get("properties").propertyNames().forEach(named::add);

        assertEquals(List.copyOf(SoutherExtension.advertised().keySet()), named);
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

    @Test
    void aSoutherMemberThatIsNotAnObjectIsSaidToBeUnread() {
        SoutherInitializationOptions read = decode(Map.of("souther", "witness"));

        assertEquals(Adequacy.Level.OFF, read.adequacy());
        assertEquals(1, read.unread().size(), read.unread().toString());
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
