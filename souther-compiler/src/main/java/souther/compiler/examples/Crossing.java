package souther.compiler.examples;

import net.unit8.raoh.Ok;
import net.unit8.raoh.Path;
import net.unit8.raoh.Result;
import net.unit8.raoh.decode.Decoder;
import souther.compiler.check.BoundaryInput;
import souther.compiler.check.BoundaryOutput;
import souther.compiler.check.CrossingMapKey;
import souther.compiler.jvm.GeneratedClass;
import souther.compiler.jvm.GeneratedClasses;
import souther.compiler.types.MapKeyRepresentation;
import souther.runtime.Sets;

import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * A value this compile built, read into the classes of an answerer that is not this compile.
 *
 * <p>What crosses is the neutral form ({@link NeutralValue}), and what reads it is the other build's
 * own derived decoder. Nothing of this compile's classes is handed over, which is the whole point:
 * a typed {@code apply} checks class identity, and two loaders that defined the same declaration
 * hold two classes that are not each other.
 *
 * <p>The walk is over {@link BoundaryInput}, which is the compiler's own answer to what a parameter
 * carries — the shape a {@link souther.compiler.check.Sig} was built with. Deciding it again here
 * from a {@code Type} would be a second reader of admissibility, free to answer differently about
 * one signature. Only the class lookup is this side's, because only that is a fact about the loader.
 *
 * <p>A nominal position is read whole. A derived decoder reads everything under the type it belongs
 * to, so a data with a list of newtypes in it crosses in one call and this walk stops there. Only
 * what stands above the outermost nominal — a bare scalar, a bare collection — is taken apart here,
 * and a scalar crosses as itself: what a neutral form holds for one is the value a typed
 * {@code apply} already takes.
 */
final class Crossing {

    private final ClassLoader into;

    Crossing(ClassLoader into) {
        this.into = into;
    }

    /**
     * {@code neutral} as {@code shape}'s value in this crossing's classes.
     *
     * @throws FixtureException         where the other build's decoder would not read it. That is the
     *                                  two builds disagreeing about a value, said as the row not
     *                                  having been handed over rather than as the model failing
     * @throws ImplementationNotReached where a class the shape names is not in these classes at all
     */
    Object crossed(BoundaryInput shape, Object neutral) {
        return switch (shape) {
            case BoundaryInput.Scalar _ -> neutral;
            case BoundaryInput.Nominal nominal -> decoded(nominal.name(), neutral);
            case BoundaryInput.ListOf list -> elements(list.element(), neutral);
            // The set a decoded position holds, built the one way the runtime builds one — a
            // `java.util` set would be a second representation of what a `Set` is.
            case BoundaryInput.SetOf set -> Sets.fromList(elements(set.element(), neutral));
            case BoundaryInput.MapOf map -> entries(map, neutral);
        };
    }

    private List<Object> elements(BoundaryInput element, Object neutral) {
        if (!(neutral instanceof List<?> written)) {
            throw new FixtureException("a collection crossing to another build's classes is written"
                    + " as a list, and this is " + shownAs(neutral));
        }
        List<Object> out = new ArrayList<>(written.size());
        for (Object e : written) {
            out.add(crossed(element, e));
        }
        return out;
    }

    /**
     * A map, key by key. A key is read by what the map-key rule already decided it is carried as, so
     * a named key runs its own type's decoder and a lexical one crosses as the text it is — the same
     * split {@code CodecGen.emitKeyDecoder} emits, asked of the shape rather than of a spelling.
     */
    private Map<Object, Object> entries(BoundaryInput.MapOf map, Object neutral) {
        if (!(neutral instanceof Map<?, ?> written)) {
            throw new FixtureException("a `Map` crossing to another build's classes is written as a"
                    + " map of its keys, and this is " + shownAs(neutral));
        }
        Map<Object, Object> out = new LinkedHashMap<>();
        for (Map.Entry<?, ?> entry : written.entrySet()) {
            out.put(key(map.key(), entry.getKey()), crossed(map.value(), entry.getValue()));
        }
        return out;
    }

    private Object key(CrossingMapKey key, Object neutral) {
        return key.representation() instanceof MapKeyRepresentation.NamedKey named
                ? decoded(named.name(), neutral)
                : neutral;
    }

    /**
     * {@code neutral} read by the type's derived {@code decoder()} in these classes.
     *
     * <p>The decoder is the one the other build emitted, so what it holds a value to is what that
     * build declared — which is exactly what a row is being run against, and is why the two builds'
     * declarations are held together before any row gets here.
     */
    Object crossed(souther.compiler.types.TypeSymbol type, Object neutral) {
        return decoded(type, neutral);
    }

    /**
     * {@code neutral} as what a behavior answers with, in this crossing's classes.
     *
     * <p>The same walk over what a signature admits, asked of the answer's side. A union's answer is
     * crossed at the case it turned out to be rather than here — {@link BoundaryOutput.Cases} is the
     * set it may be one of, and reading a value at the set would ask for what a position adds rather
     * than for the value.
     */
    Object crossed(BoundaryOutput shape, Object neutral) {
        return switch (shape) {
            case BoundaryOutput.Scalar _ -> neutral;
            case BoundaryOutput.Nominal nominal -> decoded(nominal.name(), neutral);
            case BoundaryOutput.ListOf list -> outElements(list.element(), neutral);
            case BoundaryOutput.SetOf set -> Sets.fromList(outElements(set.element(), neutral));
            case BoundaryOutput.MapOf map -> outEntries(map, neutral);
            case BoundaryOutput.Cases _ -> throw new IllegalStateException(
                    "an answer is crossed at the case it is, not at the set of cases it may be");
        };
    }

    private List<Object> outElements(BoundaryOutput element, Object neutral) {
        if (!(neutral instanceof List<?> written)) {
            throw new FixtureException("a collection crossing to another build's classes is written"
                    + " as a list, and this is " + shownAs(neutral));
        }
        List<Object> out = new ArrayList<>(written.size());
        for (Object e : written) {
            out.add(crossed(element, e));
        }
        return out;
    }

    private Map<Object, Object> outEntries(BoundaryOutput.MapOf map, Object neutral) {
        if (!(neutral instanceof Map<?, ?> written)) {
            throw new FixtureException("a `Map` crossing to another build's classes is written as a"
                    + " map of its keys, and this is " + shownAs(neutral));
        }
        Map<Object, Object> out = new LinkedHashMap<>();
        for (Map.Entry<?, ?> entry : written.entrySet()) {
            out.put(key(map.key(), entry.getKey()), crossed(map.value(), entry.getValue()));
        }
        return out;
    }

    private Object decoded(souther.compiler.types.TypeSymbol type, Object neutral) {
        Class<?> value;
        Method factory;
        try {
            value = GeneratedClasses.load(into, new GeneratedClass.Value(type));
            factory = value.getDeclaredMethod("decoder");
            factory.setAccessible(true);
        } catch (ReflectiveOperationException e) {
            throw new ImplementationNotReached("`" + type.name() + "` is not in the classes the"
                    + " implementation was built against: " + e, e);
        }
        Result<?> read;
        try {
            @SuppressWarnings("unchecked")
            Decoder<Object, ?> decoder = (Decoder<Object, ?>) factory.invoke(null);
            read = decoder.decode(neutral, Path.ROOT);
        } catch (ReflectiveOperationException | ClassCastException e) {
            throw new ImplementationNotReached("`" + type.name() + "`'s decoder could not be run in"
                    + " the classes the implementation was built against: " + e, e);
        }
        if (read instanceof Ok<?> ok) {
            return ok.value();
        }
        throw new FixtureException("`" + type.name() + "` as the implementation's own build declares"
                + " it does not read the value this row states");
    }

    /** What a value that is not the form the shape reads is called, without naming a class of it —
     *  the two builds' classes have one name between them and quoting it would say nothing. */
    private static String shownAs(Object neutral) {
        return neutral == null ? "nothing" : "a " + neutral.getClass().getSimpleName();
    }
}
