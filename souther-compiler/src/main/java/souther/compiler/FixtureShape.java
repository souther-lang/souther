package souther.compiler;

import souther.compiler.check.Symbols;
import souther.compiler.types.BoundaryInput;
import souther.compiler.types.BoundaryOutput;
import souther.compiler.types.BoundaryScalar;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;

import java.util.ArrayList;
import java.util.List;

/**
 * What a fixture may supply a value of, at one position.
 *
 * <p>A position a fixture supplies is established by a helper's parameter, by a behavior's boundary,
 * or by a row's expectation, and until now none of them said what could stand there. The reader
 * worked it out as it went, from three things that are not that question: the boundary's rule about
 * what may key a {@code Map} that crosses, whether reflection found a generated {@code decoder()},
 * and which constructors of {@link Type} it happened to have a branch for. Between them they refused
 * a {@code Map<Int, Int>} a helper takes for crossing a boundary it does not cross, and a
 * {@code RoundingMode} for a lookup that came back empty.
 *
 * <p>The question this answers is its own: a fixture is written text that becomes a value by being
 * decoded, so what may stand at such a position is what a decoder reads. That is a scalar with a
 * leaf decoder, a type whose codec was derived, or a collection of them — and a {@code Map}'s key is
 * a position of the same kind, decoded by its own type's decoder rather than parsed out of text. It
 * is not the boundary's question: nothing here crosses anything, and a {@code Map} a fixture builds
 * is a map of keys rather than a JSON object of strings.
 *
 * <p>The walk stops at a nominal, which is why an optional a data holds is nothing to do with this:
 * that data's own decoder reads its {@code ?} field, and a fixture writes {@code None} there. What
 * this refuses is an optional standing at the position itself, which is a value no decoder here
 * reads.
 *
 * <p>What a written expression can denote is a further question and not this one. A shape admitted
 * here is one a decoder would read; whether the fixture language has a way to write it is answered
 * where the expression is read.
 */
public sealed interface FixtureShape {

    /** The type in the language this shape stands for. Answered per case rather than by switching,
     *  so a case added here cannot forget it. */
    Type type();

    /** A scalar read by a leaf decoder. The six are the six a boundary writes, and for the same
     *  reason rather than by borrowing: they are the primitives a codec exists for. */
    record Scalar(BoundaryScalar scalar) implements FixtureShape {
        @Override
        public Type type() {
            return scalar.type();
        }
    }

    /** A type whose codec was derived, built by its own generated {@code decoder()}. */
    record Nominal(TypeName name) implements FixtureShape {
        @Override
        public Type type() {
            return Type.ref(name);
        }
    }

    /** A list of them. */
    record ListOf(FixtureShape element) implements FixtureShape {
        @Override
        public Type type() {
            return Type.list(element.type());
        }
    }

    /** A set of them, written as a list and deduplicated. */
    record SetOf(FixtureShape element) implements FixtureShape {
        @Override
        public Type type() {
            return Type.set(element.type());
        }
    }

    /** A map of them. Its key is a position of the same kind: a fixture writes the key as the value
     *  it is, so what reads it is that type's own decoder. */
    record MapOf(FixtureShape key, FixtureShape value) implements FixtureShape {
        @Override
        public Type type() {
            return Type.map(key.type(), value.type());
        }
    }

    /**
     * The shape a fixture may supply at a position of type {@code t}, refusing what no decoder
     * reads. {@link FixtureException} rather than a diagnostic: a fixture's failures are reported
     * against the row that wrote it.
     */
    static FixtureShape of(Type t, Symbols symbols) {
        return switch (t) {
            case Type.Prim p -> scalar(p);
            case Type.Ref r -> nominal(r.name(), symbols);
            case Type.ListOf l -> new ListOf(of(l.element(), symbols));
            case Type.SetOf s -> new SetOf(of(s.element(), symbols));
            case Type.MapOf m -> new MapOf(of(m.key(), symbols), of(m.value(), symbols));
            case Type.OptionOf o -> throw new FixtureException(
                    "`" + Type.show(o) + "` is an optional standing where a fixture supplies a value;"
                            + " absence belongs to the data that holds it, on a `?` field, where a"
                            + " fixture writes `None` or the value itself");
            case Type.TupleOf _, Type.FnOf _ -> throw new FixtureException(
                    "`" + Type.show(t) + "` has no external representation, so no decoder reads one"
                            + " and a fixture has nothing to build it through");
            case Type.Union u -> throw new FixtureException(
                    "`" + Type.show(u) + "` names several types, and a fixture supplies a value of"
                            + " one; write the case it is");
            case Type.Var _, Type.MetaVar _ -> throw new FixtureException(
                    "`" + Type.show(t) + "` is decided by each call, and a fixture is built before a"
                            + " call can decide it");
            case Type.Nothing _, Type.Never _, Type.Erroneous _ -> throw new FixtureException(
                    "`" + Type.show(t) + "` is not a type a fixture can be built against");
        };
    }

    /**
     * The shape of a position a behavior's boundary established.
     *
     * <p>A projection and not a decision: every type a boundary admits is one a fixture admits too —
     * it admits the same scalars, requires a name a model declared where this requires one whose
     * codec was derived, and requires a key that renders as text where this takes any key a decoder
     * reads. So there is nothing here that can refuse, which is the point. The position was admitted
     * where it was established, and this reads that answer rather than putting the type through the
     * walk a second time.
     */
    static FixtureShape of(BoundaryInput in) {
        return switch (in) {
            case BoundaryInput.Scalar s -> new Scalar(s.scalar());
            case BoundaryInput.Nominal n -> new Nominal(n.name());
            case BoundaryInput.ListOf l -> new ListOf(of(l.element()));
            case BoundaryInput.SetOf s -> new SetOf(of(s.element()));
            case BoundaryInput.MapOf m -> new MapOf(key(m.key()), of(m.value()));
        };
    }

    /** The same of what a behavior answers. */
    static FixtureShape of(BoundaryOutput out) {
        return switch (out) {
            case BoundaryOutput.Scalar s -> new Scalar(s.scalar());
            case BoundaryOutput.Nominal n -> new Nominal(n.name());
            case BoundaryOutput.ListOf l -> new ListOf(of(l.element()));
            case BoundaryOutput.SetOf s -> new SetOf(of(s.element()));
            case BoundaryOutput.MapOf m -> new MapOf(key(m.key()), of(m.value()));
            // A union nobody named is several types, and a fixture states a value of one of them:
            // which one is what the row writes, and it is built against that case.
            case BoundaryOutput.Cases c -> throw new IllegalStateException(
                    "`" + Type.show(c.type()) + "` names several types; a fixture states one of them");
        };
    }

    /** A key a boundary map carries, as the position a fixture writes it at. */
    private static FixtureShape key(souther.compiler.types.BoundaryMapKey key) {
        return switch (key) {
            case souther.compiler.types.BoundaryMapKey.Text _ -> new Scalar(BoundaryScalar.STRING);
            case souther.compiler.types.BoundaryMapKey.Date _ -> new Scalar(BoundaryScalar.DATE);
            case souther.compiler.types.BoundaryMapKey.DateTime _ ->
                    new Scalar(BoundaryScalar.DATETIME);
            case souther.compiler.types.BoundaryMapKey.StringNewtype n -> new Nominal(n.name());
            case souther.compiler.types.BoundaryMapKey.UnitEnum e -> new Nominal(e.name());
        };
    }

    /** Every position of a signature a fixture supplies, in order. */
    static List<FixtureShape> of(List<Type> types, Symbols symbols) {
        List<FixtureShape> shapes = new ArrayList<>(types.size());
        for (Type t : types) {
            shapes.add(of(t, symbols));
        }
        return List.copyOf(shapes);
    }

    private static FixtureShape scalar(Type.Prim prim) {
        BoundaryScalar scalar = BoundaryScalar.of(prim);
        if (scalar == null) {
            throw new FixtureException("`Raw` is the reserved type and has no decoder, so a fixture"
                    + " has nothing to build one through");
        }
        return new Scalar(scalar);
    }

    /**
     * A name a fixture builds through the codec derived for it.
     *
     * <p>Two names have none. {@code Raw} is spelled like a primitive and denotes a reference, which
     * is the whole reason the reader's {@code Raw} arm never ran — it fell through to reflection and
     * failed there instead. And a data souther-runtime implements by hand belongs to no compiled
     * module, so nothing derived a codec for it; a rounding mode is a computation's input rather
     * than a value anything reads from text.
     */
    private static FixtureShape nominal(TypeName name, Symbols symbols) {
        if (name.isPrimitive()) {
            return scalar(primitive(name));
        }
        if (TypeName.RUNTIME.equals(name.module())) {
            throw new FixtureException("`" + name.name() + "` is implemented by the runtime rather"
                    + " than derived, so it has no decoder a fixture could build one through");
        }
        if (symbols.get(name) == null) {
            throw new FixtureException("`" + name.name() + "` is not a type this example can read");
        }
        return new Nominal(name);
    }

    /** The primitive a primitive-spelled name denotes. {@code Raw} answers none, and is refused as
     *  the reserved name it is. */
    private static Type.Prim primitive(TypeName name) {
        for (Type.Prim prim : Type.Prim.values()) {
            if (Type.show(prim).equals(name.name())) {
                return prim;
            }
        }
        throw new FixtureException("`" + name.name() + "` is not a type this example can read");
    }
}
