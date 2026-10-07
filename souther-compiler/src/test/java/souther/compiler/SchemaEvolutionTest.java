package souther.compiler;

import org.junit.jupiter.api.Test;

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

    /**
     * A condition that holds of more documents is a narrowing, though each part of it grew.
     *
     * <p>{@code {"k": "y"}} was outside the condition and owed nothing; with {@code y} added to what
     * the condition allows it is inside it, and owes {@code m}, which it does not carry.
     */
    @Test
    void aConditionThatHoldsOfMoreIsANarrowing() {
        String shipped = """
                {
                  "if": { "required": ["k"], "properties": { "k": { "enum": ["x"] } } },
                  "then": { "required": ["m"] }
                }""";
        assertEquals(List.of("/if: changed where a part accepting more can make the whole accept"
                        + " less"),
                narrowings(shipped, """
                        {
                          "if": { "required": ["k"], "properties": { "k": { "enum": ["x", "y"] } } },
                          "then": { "required": ["m"] }
                        }"""));
        assertEquals(List.of("/if: changed where a part accepting more can make the whole accept"
                        + " less"),
                narrowings(shipped, """
                        {
                          "if": {
                            "required": ["k"],
                            "properties": { "k": { "enum": ["x"] }, "j": { "const": 1 } }
                          },
                          "then": { "required": ["m"] }
                        }"""),
                "and so is a key added to what the condition names");
    }

    /** A part under {@code not} accepting more is the whole refusing more. */
    @Test
    void whatANotAcceptsGrowingIsANarrowing() {
        assertEquals(List.of("/not: changed where a part accepting more can make the whole accept"
                        + " less"),
                narrowings("""
                        { "not": { "required": ["k", "m"] } }""", """
                        { "not": { "required": ["k"] } }"""));
    }

    /**
     * A branch of a {@code oneOf} may grow where no other branch can take what it takes, and not
     * where one can.
     */
    @Test
    void aBranchGrowsOnlyWhereNoOtherBranchCanShareADocument() {
        String toldApart = """
                {
                  "required": ["kind"],
                  "oneOf": [
                    { "properties": { "kind": { "const": "a" }, "v": { "enum": ["x"] } } },
                    { "properties": { "kind": { "const": "b" }, "v": { "enum": ["z"] } } }
                  ]
                }""";
        assertEquals(List.of(), narrowings(toldApart, """
                {
                  "required": ["kind"],
                  "oneOf": [
                    { "properties": { "kind": { "const": "a" }, "v": { "enum": ["x", "z"] } } },
                    { "properties": { "kind": { "const": "b" }, "v": { "enum": ["z"] } } }
                  ]
                }"""), "a document either branch takes says which by its kind");

        String alike = """
                {
                  "oneOf": [
                    { "properties": { "v": { "enum": ["x"] } } },
                    { "properties": { "v": { "enum": ["z"] } } }
                  ]
                }""";
        assertEquals(List.of("/oneOf/0: changed where a part accepting more can make the whole"
                        + " accept less"),
                narrowings(alike, """
                        {
                          "oneOf": [
                            { "properties": { "v": { "enum": ["x", "z"] } } },
                            { "properties": { "v": { "enum": ["z"] } } }
                          ]
                        }"""), "{\"v\": \"z\"} matched one branch and now matches both");
    }

    /**
     * A definition a {@code not} reaches is as it shipped, even where it is reached elsewhere as
     * well; one reached only where things may grow may grow.
     */
    @Test
    void aDefinitionReachedWhereNothingMayGrowIsAsItShipped() {
        String shipped = """
                {
                  "properties": { "a": { "$ref": "#/$defs/w" }, "b": { "$ref": "#/$defs/u" } },
                  "not": { "properties": { "c": { "$ref": "#/$defs/v" } } },
                  "$defs": {
                    "w": { "enum": ["x"] },
                    "v": { "$ref": "#/$defs/w" },
                    "u": { "enum": ["x"] }
                  }
                }""";
        assertEquals(List.of("/$defs/w: changed where a part accepting more can make the whole"
                        + " accept less"),
                narrowings(shipped, """
                        {
                          "properties": { "a": { "$ref": "#/$defs/w" }, "b": { "$ref": "#/$defs/u" } },
                          "not": { "properties": { "c": { "$ref": "#/$defs/v" } } },
                          "$defs": {
                            "w": { "enum": ["x", "y"] },
                            "v": { "$ref": "#/$defs/w" },
                            "u": { "enum": ["x", "y"] }
                          }
                        }"""));
    }

    /** A key added to an object that admits others takes the key out of what held it before. */
    @Test
    void aKeyAddedToAnOpenObjectIsANarrowing() {
        assertEquals(List.of("/properties/b: added to an object that admits other keys"),
                narrowings("""
                        {
                          "properties": { "a": { "type": "string" } },
                          "additionalProperties": { "type": "string" }
                        }""", """
                        {
                          "properties": { "a": { "type": "string" }, "b": { "type": "integer" } },
                          "additionalProperties": { "type": "string" }
                        }"""));
    }

    /** A key a document carries named {@code description} is a key, not something said in prose. */
    @Test
    void aKeyNamedDescriptionIsCompared() {
        assertEquals(List.of("/not: changed where a part accepting more can make the whole accept"
                        + " less"),
                narrowings("""
                        { "not": { "properties": { "description": { "const": 1 } } } }""", """
                        { "not": { "properties": { "description": { "const": 2 } } } }"""));
    }

    private static List<String> narrowings(String current) {
        return narrowings(SHIPPED, current);
    }

    private static List<String> narrowings(String shipped, String current) {
        return SchemaEvolution.narrowings(JSON.readTree(shipped), JSON.readTree(current));
    }
}
