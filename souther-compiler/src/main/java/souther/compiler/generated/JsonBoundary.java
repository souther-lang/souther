package souther.compiler.generated;

import souther.compiler.check.BoundaryInput;
import souther.compiler.check.CrossingMapKey;
import souther.compiler.check.BoundaryOutput;
import souther.compiler.evaluate.EvaluationContext;
import souther.compiler.jvm.GeneratedClass;
import souther.compiler.jvm.SoutherJvmAbi;
import souther.compiler.types.LeafScalar;
import souther.compiler.types.MapKeyRepresentation;
import souther.compiler.types.TypeSymbol;
import souther.runtime.Representations;
import souther.runtime.Result;
import souther.runtime.Sets;
import souther.runtime.boundary.Decoder;
import souther.runtime.boundary.Decoding;
import souther.runtime.boundary.Encoder;
import souther.runtime.boundary.Encoding;
import souther.runtime.boundary.Refusals;
import tools.jackson.databind.JsonNode;

import java.math.BigDecimal;
import java.time.Instant;
import java.time.LocalDate;
import java.time.LocalDateTime;
import java.time.LocalTime;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * A value crossing between JSON and the classes this compilation generated.
 *
 * <p>A boundary shape is not always a class. A data has a generated {@code decoder()} and
 * {@code encoder()} that read and write it whole; a primitive, a list, a set and a map have no class
 * of their own, so the decoder for one is composed here out of {@code Decoding}'s parts — the same
 * parts the generated decoders are composed of, so the two cannot read a value differently.
 *
 * <p>Nothing here says anything to a reader. What went wrong comes back as a {@link Read} or as the
 * failure it was, thrown as it was, and whoever asked decides how to say it: {@code souther run} makes a
 * message with a position in the argument vector, which is a thing only it knows about.
 */
public final class JsonBoundary {

    private JsonBoundary() {}

    /** What reading one value from JSON came to. */
    public sealed interface Read {

        /** It read, and this is the value. */
        record Value(Object value) implements Read {}

        /** The decoder refused it, and these are the refusals, at their paths. */
        record Refused(Refusals refusals) implements Read {}
    }

    /**
     * {@code raw} read as {@code shape}.
     *
     * <p>Every input a decoder refuses comes back as refusals, an array where an object belongs
     * among them. What a decoder throws is therefore not about the input: it is the platform
     * having no room for something the decoder computed — an invariant's arithmetic past what a
     * {@code BigDecimal} keeps, which is the runtime's {@code OutOfRoom} — or a defect. Neither
     * is turned into a statement about the input here; it reaches the caller as it was thrown.
     */
    public static Read read(ClassLoader loader, BoundaryInput shape, JsonNode raw) {
        return switch (decoderFor(loader, shape).decode(raw, JsonTreeReader.INSTANCE)) {
            case Result.Ok<?, Refusals>(Object value) -> new Read.Value(value);
            case Result.Err<?, Refusals>(Refusals refusals) -> new Read.Refused(refusals);
        };
    }

    /**
     * The decoder for one input type. A data's is its generated {@code decoder()}, so a nested
     * shape, an invariant and a sum's discriminator are all read exactly as they are at the
     * boundary. What is composed here is only what has no class of its own: the primitives and the
     * collections.
     */
    private static Decoder<?> decoderFor(ClassLoader loader, BoundaryInput shape) {
        return switch (shape) {
            case BoundaryInput.Scalar s -> leaf(s.scalar());
            case BoundaryInput.Nominal n -> decoderOf(loader, n.name());
            case BoundaryInput.ListOf l -> Decoding.list(decoderFor(loader, l.element()));
            case BoundaryInput.SetOf s -> Decoding.list(decoderFor(loader, s.element()))
                    .map(elements -> Sets.fromList(new ArrayList<Object>(elements),
                            EvaluationContext.checkpoint()));
            case BoundaryInput.MapOf m -> Decoding.map(decoderFor(loader, m.value()))
                    .then(Decoding.keys(keyDecoder(loader, m.key())));
        };
    }

    /**
     * The decoder for a boundary map's key: the one a generated decoder reads a key with. Which key
     * types arrive here is not decided again: the witness the map-key rule answers with travels in
     * the shape. A named key runs its own decoder, and a lexical one is its leaf, reading text.
     */
    private static Decoder<?> keyDecoder(ClassLoader loader, CrossingMapKey key) {
        return switch (key.representation()) {
            case MapKeyRepresentation.NamedKey n -> decoderOf(loader, n.name());
            case MapKeyRepresentation.Lexical l -> leaf(l.leaf());
        };
    }

    /** The leaf decoder of a scalar, the one a generated decoder reads it with. */
    private static Decoder<?> leaf(LeafScalar scalar) {
        return switch (scalar) {
            case STRING -> Decoding.string();
            case INT -> Decoding.integer();
            case BOOL -> Decoding.bool();
            case DECIMAL -> Decoding.decimal();
            case DATE -> Decoding.date();
            case TIME -> Decoding.time();
            case DATETIME -> Decoding.dateTime();
            case INSTANT -> Decoding.instant();
        };
    }

    /**
     * The {@code decoder()} of a generated class.
     *
     * <p>The name came out of the witness, so it is one a model declared and one this compilation
     * generated a class for. There is nothing here to report: a reflective failure would mean the
     * class this run emitted is not the class it emitted, which is not something a reader of the
     * boundary can say anything useful about.
     */
    private static Decoder<?> decoderOf(ClassLoader loader, TypeSymbol type) {
        String name = SoutherJvmAbi.nameOf(new GeneratedClass.Value(type)).binaryName();
        try {
            return (Decoder<?>) loader.loadClass(name).getMethod("decoder").invoke(null);
        } catch (ReflectiveOperationException e) {
            throw new IllegalStateException("`" + name + "` has no `decoder()`", e);
        }
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
                    encodeElements(loader, pkg, behavior, s.element(), (Collection<?>) result),
                    EvaluationContext.checkpoint());
            case BoundaryOutput.MapOf m -> {
                Map<String, Object> encoded = new LinkedHashMap<>();
                ((Map<?, ?>) result).forEach((k, v) -> encoded.put(encodeKey(loader, m.key(), k),
                        write(loader, pkg, behavior, m.value(), v)));
                yield Representations.sortedObject(encoded, EvaluationContext.checkpoint());
            }
            case BoundaryOutput.Nominal n ->
                    encodeThrough(loader, SoutherJvmAbi.nameOf(new GeneratedClass.Value(n.name())).binaryName(), result);
            // A union nobody named is generated as the behavior's result type, which is where its
            // encoder is (spec §jvm-anonymous-union). It is the only output with no name in the source, so it is the
            // behavior that says which class to reach for.
            case BoundaryOutput.Cases _ -> encodeThrough(loader,
                    SoutherJvmAbi.nameOf(new GeneratedClass.BehaviorResult(pkg, behavior)).binaryName(), result);
        };
    }

    /**
     * A map's key, written as the text it crosses as: the leaf's own form for a primitive, and the
     * type's derived encoder for a named key, whatever that name wraps. The same two the bytecode
     * encoder writes ({@code CodecGen.pushKeyRenderer}), which is what keeps the two paths from
     * spelling a key differently.
     */
    private static String encodeKey(ClassLoader loader, CrossingMapKey key, Object value) {
        return (String) switch (key.representation()) {
            case MapKeyRepresentation.Lexical l -> encodeLeaf(l.leaf(), value);
            case MapKeyRepresentation.NamedKey n ->
                    encodeThrough(loader, SoutherJvmAbi.nameOf(new GeneratedClass.Value(n.name())).binaryName(), value);
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
            case STRING -> Encoding.string().encode((String) value);
            case INT -> Encoding.integer().encode((Long) value);
            case BOOL -> Encoding.bool().encode((Boolean) value);
            case DECIMAL -> Encoding.decimal()
                    .encode(Representations.canonicalNumber((BigDecimal) value,
                            EvaluationContext.checkpoint()));
            case DATE -> Encoding.date().encode((LocalDate) value);
            case TIME -> Encoding.time().encode((LocalTime) value);
            case DATETIME -> Encoding.dateTime().encode((LocalDateTime) value);
            case INSTANT -> Encoding.instant().encode((Instant) value);
        };
    }
}
