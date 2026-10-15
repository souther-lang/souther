package souther.compiler;

import tools.jackson.databind.JsonNode;

import java.util.ArrayList;
import java.util.List;

/**
 * Where a {@code $ref} in the shipped schema points, read as the JSON Pointer it is.
 *
 * <p>The one reading of a reference for every check that follows one. A reference is a pointer into
 * the document, and a pointer can go past the definition it starts at — {@code #/$defs/weakening/items}
 * is what one definition holds, not a definition of its own. Taken apart by each check for itself,
 * such a reference is read as its last step or as everything after {@code $defs}, and either names
 * a definition the schema does not have.
 */
public final class SchemaReference {

    private static final String DEFINITIONS = "$defs";

    private SchemaReference() {
    }

    /** The part of {@code schema} that {@code reference} points at; asserted to exist. */
    public static JsonNode resolve(JsonNode schema, String reference) {
        JsonNode at = schema;
        for (String step : steps(reference)) {
            JsonNode next = at.isArray() ? at.get(Integer.parseInt(step)) : at.get(step);
            if (next == null) {
                throw new AssertionError("the schema refers to " + reference
                        + " and has nothing there");
            }
            at = next;
        }
        return at;
    }

    /**
     * The top-level definition {@code reference} points into, or null where it points somewhere
     * that is no definition.
     *
     * <p>The whole definition and not the part inside it. Whatever is asked of the part is asked of
     * the definition holding it by any check that keeps a definition as one unit.
     */
    public static String definition(String reference) {
        List<String> steps = steps(reference);
        return steps.size() >= 2 && steps.get(0).equals(DEFINITIONS) ? steps.get(1) : null;
    }

    /** The steps of a pointer within this document, each unescaped as RFC 6901 says. */
    private static List<String> steps(String reference) {
        if (!reference.startsWith("#/")) {
            throw new AssertionError("a reference this does not follow: " + reference);
        }
        List<String> out = new ArrayList<>();
        for (String step : reference.substring(2).split("/", -1)) {
            out.add(step.replace("~1", "/").replace("~0", "~"));
        }
        return out;
    }
}
