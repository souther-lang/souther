package souther.raoh;

import org.jspecify.annotations.Nullable;
import souther.runtime.boundary.TreeReader;
import tools.jackson.databind.JsonNode;

import java.util.Map;

/**
 * The reader of a Jackson {@code JsonNode} tree. A number is handed over in the carrier the node
 * holds it in, so a fraction a parser read as a {@code double} reaches the decoder as one, and is
 * refused where a {@code Decimal} stands (spec {@code [#codec-generation]}). A missing node and
 * {@code null} are the tree's null.
 */
final class JsonNodeReader implements TreeReader {

    static final JsonNodeReader INSTANCE = new JsonNodeReader();

    private JsonNodeReader() {}

    @Override
    public Shape shapeOf(Object node) {
        JsonNode json = (JsonNode) node;
        return json.isNull() || json.isMissingNode() ? Shape.NULL
                : json.isObject() ? Shape.OBJECT
                : json.isArray() ? Shape.ARRAY
                : Shape.SCALAR;
    }

    @Override
    public @Nullable Object member(Object object, String name) {
        JsonNode value = ((JsonNode) object).get(name);
        return value == null || value.isNull() || value.isMissingNode() ? null : value;
    }

    @Override
    public Iterable<? extends Map.Entry<?, ?>> members(Object object) {
        return ((JsonNode) object).properties();
    }

    /** The array's elements: the node walks them itself. */
    @Override
    public Iterable<?> elements(Object array) {
        return (JsonNode) array;
    }

    @Override
    public Object scalar(Object node) {
        JsonNode json = (JsonNode) node;
        if (json.isString()) {
            return json.stringValue();
        }
        if (json.isBoolean()) {
            return json.booleanValue();
        }
        if (json.isNumber()) {
            return json.numberValue();
        }
        return json;
    }

    @Override
    public String describe(Object node) {
        return switch (((JsonNode) node).getNodeType()) {
            case ARRAY -> "array";
            case BINARY -> "binary";
            case BOOLEAN -> "boolean";
            case MISSING -> "missing";
            case NULL -> "null";
            case NUMBER -> "number";
            case OBJECT -> "object";
            case POJO -> "pojo";
            case STRING -> "string";
        };
    }
}
