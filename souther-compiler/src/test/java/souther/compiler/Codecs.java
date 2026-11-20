package souther.compiler;

import net.unit8.raoh.Ok;
import net.unit8.raoh.Path;
import net.unit8.raoh.Result;
import net.unit8.raoh.decode.Decoder;
import souther.raoh.RaohBinding;
import souther.runtime.Behavior;
import souther.runtime.boundary.Encoder;

/**
 * Reflective access to a compiled module's derived codecs and behaviors. Souther emits these
 * as static factories ({@code decoder()}/{@code encoder()}) and no-arg behavior classes whose
 * generic parameters are gone at the reflection boundary. This helper confines the unavoidable
 * unchecked casts to private methods so the tests themselves stay free of raw types.
 *
 * <p>A derived decoder is read here through the Raoh binding, so what a test asserts of a refusal
 * is what a Raoh user is told: the binding is the one place its codes and paths are written.
 */
final class Codecs {

    private Codecs() {}

    /** What a decoder reads: plain Java values, a Jackson tree, or a jOOQ row. */
    enum Source { PLAIN, JSON, RECORD }

    static final Source JSON = Source.JSON;
    static final Source RECORD = Source.RECORD;

    @SuppressWarnings("unchecked")
    private static souther.runtime.boundary.Decoder<Object> asDerived(Object factoryResult) {
        return (souther.runtime.boundary.Decoder<Object>) factoryResult;
    }

    @SuppressWarnings("unchecked")
    private static Decoder<Object, ?> bound(souther.runtime.boundary.Decoder<Object> derived,
                                           Source source) {
        return switch (source) {
            case PLAIN -> RaohBinding.decoder(derived);
            case JSON -> (Decoder<Object, ?>) (Decoder<?, ?>) RaohBinding.jsonDecoder(derived);
            case RECORD -> (Decoder<Object, ?>) (Decoder<?, ?>) RaohBinding.recordDecoder(derived);
        };
    }

    @SuppressWarnings("unchecked")
    private static Encoder<Object, ?> asEncoder(Object factoryResult) {
        return (Encoder<Object, ?>) factoryResult;
    }

    @SuppressWarnings("unchecked")
    private static Behavior<Object, Object> asBehavior(Object instance) {
        return (Behavior<Object, Object>) instance;
    }

    /** The named class's own {@code decoder()}, unbound. */
    static souther.runtime.boundary.Decoder<Object> derived(ClassLoader loader, String className)
            throws Exception {
        return asDerived(loader.loadClass(className).getMethod("decoder").invoke(null));
    }

    static Decoder<Object, ?> decoder(ClassLoader loader, String className, Source source) throws Exception {
        return bound(derived(loader, className), source);
    }

    static Decoder<Object, ?> decoder(ClassLoader loader, String className) throws Exception {
        return decoder(loader, className, Source.PLAIN);
    }

    static Decoder<Object, ?> decoder(Class<?> clazz) throws Exception {
        return bound(asDerived(clazz.getMethod("decoder").invoke(null)), Source.PLAIN);
    }

    static Encoder<Object, ?> encoder(ClassLoader loader, String className) throws Exception {
        return asEncoder(loader.loadClass(className).getMethod("encoder").invoke(null));
    }

    static Encoder<Object, ?> encoder(Class<?> clazz) throws Exception {
        return asEncoder(clazz.getMethod("encoder").invoke(null));
    }

    /** Decode {@code raw} through the named class's {@code decoder}. */
    static Result<?> decode(ClassLoader loader, String className, Object raw) throws Exception {
        return decoder(loader, className).decode(raw, Path.ROOT);
    }

    /** Decode {@code raw}, read as {@code source}, through the named class's {@code decoder}. */
    static Result<?> decode(ClassLoader loader, String className, Source source, Object raw) throws Exception {
        return decoder(loader, className, source).decode(raw, Path.ROOT);
    }

    /** Decode {@code raw} through a class's {@code decoder}. */
    static Result<?> decode(Class<?> clazz, Object raw) throws Exception {
        return decoder(clazz).decode(raw, Path.ROOT);
    }

    /** Decode and unwrap the success value; the cast fails if the result is an error. */
    static Object decoded(ClassLoader loader, String className, Object raw) throws Exception {
        return ((Ok<?>) decode(loader, className, raw)).value();
    }

    /** Decode and unwrap the success value; the cast fails if the result is an error. */
    static Object decoded(Class<?> clazz, Object raw) throws Exception {
        return ((Ok<?>) decode(clazz, raw)).value();
    }

    /** Encode {@code value} through the named class's {@code encoder} factory. */
    static Object encode(ClassLoader loader, String className, Object value) throws Exception {
        return encoder(loader, className).encode(value);
    }

    /** Encode {@code value} through a class's {@code encoder} factory. */
    static Object encode(Class<?> clazz, Object value) throws Exception {
        return encoder(clazz).encode(value);
    }

    /** Apply a reflectively-instantiated behavior to an input. */
    static Object apply(Object behavior, Object input) {
        return asBehavior(behavior).apply(input);
    }
}
