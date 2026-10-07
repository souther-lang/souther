package souther.compiler;

import org.junit.jupiter.api.Test;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What {@link SchemaEvolution} lets a frozen schema become, one way of changing it at a time.
 *
 * <p>Each shape on its own, because the shipped schemas are what it is otherwise run over and they
 * take one or two of these at most: the copies match the files they were taken from, or differ by a
 * word added to an enum. A comparison that missed a narrowing no shipped schema has made yet would
 * pass there until somebody made it.
 */
class SchemaEvolutionTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String SHIPPED = """
            {
              "type": "object",
              "description": "As it shipped.",
              "required": ["a"],
              "additionalProperties": false,
              "properties": {
                "a": { "type": "string" },
                "b": { "enum": ["x", "y"] }
              },
              "$defs": {
                "c": { "type": "integer", "minimum": 0 }
              }
            }""";

    @Test
    void theSameSchemaNarrowsNothing() {
        assertEquals(List.of(), narrowings(SHIPPED));
    }

    @Test
    void whatGrowsTheDocumentsNarrowsNothing() {
        assertEquals(List.of(), narrowings("""
                {
                  "type": "object",
                  "description": "Said again, differently.",
                  "required": [],
                  "additionalProperties": false,
                  "properties": {
                    "a": { "type": "string", "description": "A key described." },
                    "b": { "enum": ["y", "x", "z"] },
                    "d": { "type": "string" }
                  },
                  "$defs": {
                    "c": { "type": "integer", "minimum": 0 },
                    "e": { "type": "string" }
                  }
                }"""));
    }

    @Test
    void aKeyMadeRequiredIsANarrowing() {
        assertEquals(List.of("/required: now requires [b]"), narrowings("""
                {
                  "type": "object",
                  "required": ["a", "b"],
                  "additionalProperties": false,
                  "properties": {
                    "a": { "type": "string" },
                    "b": { "enum": ["x", "y"] }
                  },
                  "$defs": {
                    "c": { "type": "integer", "minimum": 0 }
                  }
                }"""));
    }

    @Test
    void aWordTakenOutIsANarrowing() {
        assertEquals(List.of("/properties/b/enum: no longer allows [y]"), narrowings("""
                {
                  "type": "object",
                  "required": ["a"],
                  "additionalProperties": false,
                  "properties": {
                    "a": { "type": "string" },
                    "b": { "enum": ["x"] }
                  },
                  "$defs": {
                    "c": { "type": "integer", "minimum": 0 }
                  }
                }"""));
    }

    @Test
    void aKeyOrADefinitionTakenOutIsANarrowing() {
        assertEquals(List.of("/properties/b: no longer here", "/$defs/c: no longer here"),
                narrowings("""
                        {
                          "type": "object",
                          "required": ["a"],
                          "additionalProperties": false,
                          "properties": {
                            "a": { "type": "string" }
                          },
                          "$defs": {}
                        }"""));
    }

    /** A constraint tightened, and a keyword the schema did not have, are both not as shipped. */
    @Test
    void anythingElseChangedIsANarrowing() {
        assertEquals(List.of("/properties/a/pattern: not in what shipped",
                        "/$defs/c/minimum: 0 shipped and 1 now"),
                narrowings("""
                        {
                          "type": "object",
                          "required": ["a"],
                          "additionalProperties": false,
                          "properties": {
                            "a": { "type": "string", "pattern": "^x" },
                            "b": { "enum": ["x", "y"] }
                          },
                          "$defs": {
                            "c": { "type": "integer", "minimum": 1 }
                          }
                        }"""));
    }

    private static List<String> narrowings(String current) {
        JsonNode shipped = JSON.readTree(SHIPPED);
        return SchemaEvolution.narrowings(shipped, JSON.readTree(current));
    }
}
