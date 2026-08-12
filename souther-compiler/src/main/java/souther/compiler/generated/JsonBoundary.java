package souther.compiler.generated;

import souther.compiler.check.BoundaryInput;
import souther.compiler.check.BoundaryMapKey;
import souther.compiler.check.BoundaryOutput;
import souther.compiler.codegen.Backend;
import souther.compiler.types.LeafScalar;
import souther.compiler.types.MapKeyRepresentation;
import souther.compiler.types.TemporalRule;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;
import souther.runtime.Representations;
import souther.runtime.Sets;
import souther.runtime.Temporals;

import net.unit8.raoh.Err;
import net.unit8.raoh.Issues;
import net.unit8.raoh.Ok;
import net.unit8.raoh.Result;
import net.unit8.raoh.decode.Decoder;
import net.unit8.raoh.decode.ObjectDecoders;
import net.unit8.raoh.decode.builtin.StringDecoder;
import net.unit8.raoh.decode.builtin.TemporalDecoder;
import net.unit8.raoh.encode.Encoder;
import net.unit8.raoh.encode.ObjectEncoders;
import net.unit8.raoh.json.JsonDecoders;
import tools.jackson.databind.JsonNode;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * A value crossing between JSON and the classes this compilation generated.
 *
 * <p>A boundary shape is not always a class. A data has a generated {@code jsonDecoder()} and
 * {@code encoder()} that read and write it whole; a primitive, a list, a set and a map have no class
 * of their own, so the decoder for one is composed here out of the ones that do. That composition is
 * the same question the generated codecs answer for a data's fields, and it is answered in one place
 * so the two cannot spell a value differently — {@code CodecGen} emits it as bytecode, and this is
 * the same rules in Java for the shapes no class was emitted for.
 *
 * <p>Nothing here says anything to a reader. What went wrong comes back as a {@link Read} or as the
 * reflective failure it was, and whoever asked decides how to say it: {@code souther run} makes a
 * message with a position in the argument vector, which is a thing only it knows about.
 */
public final class JsonBoundary {

    private JsonBoundary() {}

    /** What reading one value from JSON came to. */
    public sealed interface Read {

        /** It read, and this is the value. */
        record Value(Object value) implements Read {}

        /** The decoder refused it, and these are the issues it found, at their paths. */
        record Refused(Issues issues) implements Read {}

        /**
         * It is not even the shape the decoder reads — an array where an object belongs — which the
         * decoder reports by throwing rather than as an issue. {@code type} is the declared type as
         * it is written, for a caller that wants to name it.
         */
        record Malformed(String type) implements Read {}
    }

    /** {@code raw} read as {@code shape}. */
    public static Read read(ClassLoader loader, BoundaryInput shape, JsonNode raw) {
        Decoder<JsonNode, ?> decoder = decoderFor(loader, shape);
        Result<?> result;
        try {
            result = decoder.decode(raw, net.unit8.raoh.Path.ROOT);
        } catch (RuntimeException _) {
            return new Read.Malformed(Type.show(shape.type()));
        }
        return result instanceof Ok<?> ok
                ? new Read.Value(ok.value())
                : new Read.Refused(((Err<?>) result).issues());
    }

    /** Whether {@code raw} reads as {@code shape} at all. */
    public static boolean reads(ClassLoader loader, BoundaryInput shape, JsonNode raw) {
        return read(loader, shape, raw) instanceof Read.Value;
    }

    /**
     * The decoder for one input type, over the JSON source. {@code --input} is JSON, so the decoders
     * have to be the ones the boundary reads JSON with: a temporal arrives as an ISO string and is
     * parsed, not handed over as a {@code java.time} value. Reading JSON with the neutral-source
     * decoders is what made a {@code Date} input impossible — anywhere, as a parameter or inside a
     * data (issue #119).
     *
     * <p>A data delegates to its generated {@code jsonDecoder()}, so a nested shape, an invariant and
     * a sum's discriminator are all read exactly as they are at the boundary. What is composed here
     * is only what has no class of its own: the primitives and the collections.
     */
    private static Decoder<JsonNode, ?> decoderFor(ClassLoader loader, BoundaryInput shape) {
        return switch (shape) {
            case BoundaryInput.Scalar s -> leafDecoder(s.scalar());
            case BoundaryInput.Nominal n -> codecOf(loader, n.name(), "jsonDecoder");
            case BoundaryInput.ListOf l -> JsonDecoders.list(decoderFor(loader, l.element()));
            case BoundaryInput.SetOf s -> JsonDecoders.list(decoderFor(loader, s.element()))
                    .map(elements -> Sets.fromList(new ArrayList<Object>(elements)));
            case BoundaryInput.MapOf m -> {
                Decoder<Object, ?> key = keyDecoder(loader, m.key());
                yield JsonDecoders.map(decoderFor(loader, m.value()))
                        .flatMapWithPath((entries, path) -> rekey(key, entries, path));
            }
        };
    }

    /**
     * The decoder for a boundary map's key. A key reaches this already read out of the JSON object
     * that carried it, so what it decodes from is a string rather than a {@code JsonNode} — the
     * neutral source, whichever source the map itself came from. This is the decoder
     * {@code CodecGen.emitKeyDecoder} builds, in Java.
     *
     * <p>Which key types arrive here is not decided again, and is not asked again either: the witness
     * the map-key rule answers with travels in the shape. A named key runs its own decoder, and a
     * lexical one is the string leaf, parsed for a temporal.
     */
    private static Decoder<Object, ?> keyDecoder(ClassLoader loader, BoundaryMapKey key) {
        return switch (key.representation()) {
            case MapKeyRepresentation.NamedKey n -> codecOf(loader, n.name(), "decoder");
            case MapKeyRepresentation.Text _ -> text();
            // Through the same rules a field's text goes through, for the same reason.
            case MapKeyRepresentation.Lexical l -> temporal(text(), l.leaf());
        };
    }

    /** The string leaf a key is read through. Text arriving from outside is canonical, which is what
     *  the leaf makes it (ADR-0096). */
    private static StringDecoder<Object> text() {
        return ObjectDecoders.string().normalize();
    }

    /**
     * A decoded {@code Map<String, V>} rekeyed by the key type's own decoder, which is where a key's
     * invariant is enforced and a temporal key is parsed.
     *
     * <p>A bad key is reported at that key's own path, and every key is read before the result is
     * settled, so a map with two bad keys says so about both. A {@code String} key is rekeyed like
     * any other: the keys of a decoded object do not pass the string leaf, so leaving them alone is
     * the one place a boundary would hand over text it had not made canonical.
     *
     * <p>Two keys that decode to one key are refused rather than collapsed. Making a key canonical
     * is what lets an object arrive with the same key written twice, and a map holding one entry
     * where the input wrote two is a value the input never described — so the second is a failure at
     * its own key, not the winner of an overwrite.
     */
    private static Result<Map<Object, Object>> rekey(Decoder<Object, ?> key, Map<String, ?> entries,
                                                     net.unit8.raoh.Path path) {
        Map<Object, Object> out = new LinkedHashMap<>();
        Issues issues = Issues.EMPTY;
        for (Map.Entry<String, ?> entry : entries.entrySet()) {
            net.unit8.raoh.Path at = path.append(entry.getKey());
            Result<?> decoded = key.decode(entry.getKey(), at);
            if (decoded instanceof Err<?> err) {
                issues = issues.merge(err.issues());
                continue;
            }
            Object rekeyed = ((Ok<?>) decoded).value();
            if (out.containsKey(rekeyed)) {
                issues = issues.merge(((Err<?>) Result.fail(at, DUPLICATE_KEY, DUPLICATE_KEY_MESSAGE))
                        .issues());
            } else {
                out.put(rekeyed, entry.getValue());
            }
        }
        return issues.isEmpty() ? new Ok<>(out) : new Err<>(issues);
    }

    /** What a key colliding with one already read is reported as — the code and the wording the
     *  generated rekey helper uses, so the two paths refuse the same input the same way. */
    private static final String DUPLICATE_KEY = "duplicate_key";
    private static final String DUPLICATE_KEY_MESSAGE = "two keys are the same key once decoded";

    /**
     * The named static decoder factory of a generated class — {@code jsonDecoder} for a value read
     * from JSON, {@code decoder} for a map key, which is read from the string the object carried.
     * Either erases at the reflection boundary.
     *
     * <p>The name came out of the witness, so it is one a model declared and one this compilation
     * generated a class for, and that class carries both factories. There is nothing here to report:
     * a reflective failure would mean the class this run emitted is not the class it emitted, which
     * is not something a reader of the boundary can say anything useful about.
     */
    private static <I> Decoder<I, ?> codecOf(ClassLoader loader, TypeName type, String factory) {
        try {
            @SuppressWarnings("unchecked")
            Decoder<I, ?> decoder = (Decoder<I, ?>)
                    loader.loadClass(type.qualified()).getMethod(factory).invoke(null);
            return decoder;
        } catch (ReflectiveOperationException e) {
            throw new IllegalStateException("`" + type.qualified() + "` has no `" + factory + "()`", e);
        }
    }

    /** A scalar over the JSON source. {@code JsonDecoders} has no temporal factory — in JSON a
     *  temporal is a string that is then parsed — so a date reads as {@code string().date()}, the
     *  same two steps the generated JSON decoder takes, and through the same rules. */
    private static Decoder<JsonNode, ?> leafDecoder(LeafScalar scalar) {
        return switch (scalar) {
            case STRING -> JsonDecoders.string();
            case INT -> JsonDecoders.long_();
            case BOOL -> JsonDecoders.bool();
            case DECIMAL -> JsonDecoders.decimal();
            case DATE, TIME, DATETIME, INSTANT -> temporal(JsonDecoders.string(), scalar);
        };
    }

    /**
     * A temporal read from text, under the rules the type has wherever it arrives
     * ({@link TemporalRule}).
     *
     * <p>These were {@code string().time()} and its siblings, spelled out beside the generated
     * decoder's own — so a top-level {@code Time} argument took {@code 09:00:00.5} and a top-level
     * {@code Instant} took a leap second, both of which the same types refuse at a data's field. A
     * rule that changes with the way in is not the type's rule, and this reads the one table rather
     * than restating it a third time.
     */
    private static <I> Decoder<I, ?> temporal(StringDecoder<I> text, LeafScalar scalar) {
        TemporalRule rule = TemporalRule.of(scalar);
        StringDecoder<I> guarded = rule.guardsText()
                ? text.refine(Temporals::notALeapSecond, TemporalRule.REFUSED, TemporalRule.LEAP_SECOND)
                : text;
        TemporalDecoder<I, ?> parsed = switch (scalar) {
            case DATE -> guarded.date();
            case TIME -> guarded.time();
            case DATETIME -> guarded.dateTime();
            case INSTANT -> guarded.iso8601();
            case STRING, INT, BOOL, DECIMAL ->
                    throw new IllegalStateException(scalar + " is not a temporal");
        };
        return rule.guardsValue()
                ? parsed.refine(Temporals::toTheSecond, TemporalRule.REFUSED, TemporalRule.SUB_SECOND)
                : parsed;
    }

    /**
     * The output as its declared type writes it. Which encoder that is follows the type the behavior
     * declared, never the class the answer happens to have arrived in: a case of a sum carries no
     * discriminator on its own encoder — only the sum's writes one — so taking the encoder off the
     * runtime value would answer a form the same sum's decoder then refuses.
     *
     * <p>Encoding descends the value by recursion, so a value that nests deeply enough runs the stack
     * out before the writer ever counts a level. A behavior can build a value deeper than anything it
     * was handed, so a {@code StackOverflowError} is reachable from input the boundary accepted, and
     * it is left for the caller to catch and name.
     */
    public static Object write(ClassLoader loader, String pkg, String behavior,
                               BoundaryOutput out, Object result) {
        return switch (out) {
            case BoundaryOutput.Scalar s -> encodeLeaf(s.scalar(), result);
            // A collection output is encoded element by element: the runtime value is a plain
            // Collection/Map, so it carries no encoder() of its own — its elements do.
            case BoundaryOutput.ListOf l ->
                    encodeElements(loader, pkg, behavior, l.element(), (Collection<?>) result);
            // A Set and a Map are put in the order their encoded members give ([#collections]), which
            // is done here as well as in the generated codecs because this is where the shape is still
            // known: encoded, a Set and a List are both a java.util.List, and only one is reordered.
            case BoundaryOutput.SetOf s -> Representations.sortedArray(
                    encodeElements(loader, pkg, behavior, s.element(), (Collection<?>) result));
            case BoundaryOutput.MapOf m -> {
                Map<String, Object> encoded = new LinkedHashMap<>();
                ((Map<?, ?>) result).forEach((k, v) -> encoded.put(encodeKey(loader, m.key(), k),
                        write(loader, pkg, behavior, m.value(), v)));
                yield Representations.sortedObject(encoded);
            }
            case BoundaryOutput.Nominal n ->
                    encodeThrough(loader, n.name().qualified(), result);
            // A union nobody named is generated as the behavior's result type, which is where its
            // encoder is (spec §jvm-anonymous-union). It is the only output with no name in the source, so it is the
            // behavior that says which class to reach for.
            case BoundaryOutput.Cases c -> encodeThrough(loader,
                    pkg + "." + Backend.behaviorResultClass(behavior), result);
        };
    }

    /**
     * A map's key, written as the text it crosses as: the leaf's own form for a primitive, and the
     * type's derived encoder for a named key, whatever that name wraps. The same two the bytecode
     * encoder writes ({@code CodecGen.pushKeyRenderer}), which is what keeps the two paths from
     * spelling a key differently.
     */
    private static String encodeKey(ClassLoader loader, BoundaryMapKey key, Object value) {
        return (String) switch (key.representation()) {
            case MapKeyRepresentation.Lexical l -> encodeLeaf(l.leaf(), value);
            case MapKeyRepresentation.NamedKey n -> encodeThrough(loader, n.name().qualified(), value);
        };
    }

    /** {@code result} through the derived {@code encoder()} of the named generated class. Every type
     *  a witness names has one, and so does the class a behavior's anonymous answer is generated as,
     *  so this reads what was emitted rather than asking whether it was. */
    private static Object encodeThrough(ClassLoader loader, String className, Object result) {
        try {
            @SuppressWarnings("unchecked")   // the generated class's encoder() erases at the reflection boundary
            Encoder<Object, ?> encoder = (Encoder<Object, ?>)
                    loader.loadClass(className).getMethod("encoder").invoke(null);
            return encoder.encode(result);
        } catch (ReflectiveOperationException e) {
            throw new IllegalStateException("`" + className + "` has no `encoder()`", e);
        }
    }

    private static List<Object> encodeElements(ClassLoader loader, String pkg, String behavior,
                                               BoundaryOutput element, Collection<?> values) {
        List<Object> encoded = new ArrayList<>(values.size());
        for (Object v : values) {
            encoded.add(write(loader, pkg, behavior, element, v));
        }
        return encoded;
    }

    private static Object encodeLeaf(LeafScalar scalar, Object value) {
        return switch (scalar) {
            case STRING -> ObjectEncoders.string().encode((String) value);
            case INT -> ObjectEncoders.long_().encode((Long) value);
            case BOOL -> ObjectEncoders.bool().encode((Boolean) value);
            case DECIMAL -> ObjectEncoders.decimal()
                    .encode(Representations.canonicalNumber((java.math.BigDecimal) value));
            case DATE -> ObjectEncoders.date().encode((java.time.LocalDate) value);
            case TIME -> ObjectEncoders.time().encode((java.time.LocalTime) value);
            case DATETIME -> ObjectEncoders.dateTime().encode((java.time.LocalDateTime) value);
            case INSTANT -> ObjectEncoders.iso8601().encode((java.time.Instant) value);
        };
    }
}
