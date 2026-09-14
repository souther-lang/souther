package souther.compiler.publish;

import org.junit.jupiter.api.Test;

import souther.compiler.report.AdequacyReport;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every field this compiler decides the order of is a field the document has, and holds many.
 *
 * <p>One direction and not the other. Which arrays have an order of this compiler's is a decision
 * about the contract that nothing in the schema records — an array of words can be in the order
 * somebody wrote them as readily as in one this compiler chose — so the decision is written down
 * beside the orders and the schema is asked whether it agrees, rather than being asked to produce
 * the list.
 *
 * <p>What that catches is a name that has gone stale. A field renamed in the schema and not in the
 * declaration leaves the check that a writer crosses looking at a name nothing writes, which is a
 * check that passes by having nothing to hold.
 */
class EveryFieldThisCompilerOrdersIsARepeatedFieldOfTheDocumentTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String SCHEMA = "/souther/adequacy-schema-"
            + AdequacyReport.SCHEMA_VERSION + ".json";

    @Test
    void eachOfThemIsAnArrayTheSchemaDescribes() {
        JsonNode schema = schema();
        List<String> missing = new ArrayList<>();
        for (String field : PublicationOrders.CANONICALLY_ARRANGED_FIELDS) {
            JsonNode described = anywhereUnder(schema, field);
            if (described == null || !"array".equals(described.path("type").asString(null))) {
                missing.add(field);
            }
        }

        assertTrue(!PublicationOrders.CANONICALLY_ARRANGED_FIELDS.isEmpty(),
                "no field is said to be ordered by this compiler, so this holds nothing");
        assertEquals(List.of(), missing,
                "a field this compiler says it decides the order of is not an array of the"
                        + " document, so the check that its writer crosses is looking at a name"
                        + " nothing writes");
    }

    /** The description of {@code field} wherever the schema gives one, which is under whichever
     *  object holds it. */
    private static JsonNode anywhereUnder(JsonNode node, String field) {
        if (node.isObject()) {
            JsonNode properties = node.get("properties");
            if (properties != null && properties.has(field)) {
                return properties.get(field);
            }
            for (JsonNode child : node.values()) {
                JsonNode found = anywhereUnder(child, field);
                if (found != null) {
                    return found;
                }
            }
        } else if (node.isArray()) {
            for (JsonNode child : node.values()) {
                JsonNode found = anywhereUnder(child, field);
                if (found != null) {
                    return found;
                }
            }
        }
        return null;
    }

    private static JsonNode schema() {
        try (InputStream in = AdequacyReport.class.getResourceAsStream(SCHEMA)) {
            assertNotNull(in, SCHEMA + " ships beside the compiler");
            return JSON.readTree(new String(in.readAllBytes(), StandardCharsets.UTF_8));
        } catch (IOException e) {
            throw new AssertionError(e);
        }
    }
}
