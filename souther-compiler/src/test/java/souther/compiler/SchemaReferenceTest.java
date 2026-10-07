package souther.compiler;

import org.junit.jupiter.api.Test;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

/** A {@code $ref} read as the pointer it is, past the definition it starts at. */
class SchemaReferenceTest {

    private static final JsonNode SCHEMA = JsonMapper.builder().build().readTree("""
            {
              "$defs": {
                "w": { "type": "array", "items": { "enum": ["x"] } },
                "a/b": { "const": 1 }
              },
              "properties": { "p": { "type": "string" } }
            }""");

    @Test
    void aPointerPastADefinitionReachesThePartInsideIt() {
        assertEquals("[\"x\"]",
                SchemaReference.resolve(SCHEMA, "#/$defs/w/items").get("enum").toString());
        assertEquals("w", SchemaReference.definition("#/$defs/w/items"),
                "and points into the definition holding it");
    }

    @Test
    void aStepIsUnescapedAsAPointerSays() {
        assertEquals(1, SchemaReference.resolve(SCHEMA, "#/$defs/a~1b").get("const").asInt());
        assertEquals("a/b", SchemaReference.definition("#/$defs/a~1b"));
    }

    @Test
    void aPointerOutsideTheDefinitionsIsIntoNoDefinition() {
        assertEquals("string",
                SchemaReference.resolve(SCHEMA, "#/properties/p").get("type").asString());
        assertNull(SchemaReference.definition("#/properties/p"));
    }

    @Test
    void aPointerToNothingIsRefused() {
        assertThrows(AssertionError.class, () -> SchemaReference.resolve(SCHEMA, "#/$defs/v"));
    }
}
