package souther.compiler;

import souther.compiler.check.Symbols;
import souther.compiler.check.BoundaryInput;
import souther.compiler.check.BoundaryOutput;
import souther.compiler.types.LeafScalar;
import souther.compiler.types.MapKeyRepresentation;
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
    record Scalar(LeafScalar scalar) implements FixtureShape {
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

    /**
     * The shape a whole answer is written as, or null where the answer is several types.
     *
     * <p>Partial, and named for it. A union nobody named is not one shape: which of its members a
     * value is is what the row writes, and the row is built against that case. Every other answer is
     * one shape, and projects as an input does.
     */
    static FixtureShape ofWholeAnswer(BoundaryOutput out) {
        return switch (out) {
            case BoundaryOutput.Scalar s -> new Scalar(s.scalar());
            case BoundaryOutput.Nominal n -> new Nominal(n.name());
            // Carried outward rather than answered for at the top. Nothing today writes a union
            // anywhere but a behavior's own answer — `|` belongs to the written return type and a
            // composition merges its retired cases there — so an element that is several types does
            // not arrive. What this keeps is that it could not be swallowed if it did: a `ListOf`
            // holding nothing is a shape whose reader would find out later and elsewhere.
            case BoundaryOutput.ListOf l -> wrapping(ofWholeAnswer(l.element()), ListOf::new);
            case BoundaryOutput.SetOf s -> wrapping(ofWholeAnswer(s.element()), SetOf::new);
            case BoundaryOutput.MapOf m -> wrapping(ofWholeAnswer(m.value()),
                    value -> new MapOf(key(m.key()), value));
            case BoundaryOutput.Cases _ -> null;
        };
    }

    /** {@code held} in its container, or nothing where there was nothing to hold. */
    private static FixtureShape wrapping(FixtureShape held,
                                         java.util.function.Function<FixtureShape, FixtureShape> in) {
        return held == null ? null : in.apply(held);
    }

    /** A key a boundary map carries, as the position a fixture writes it at. */
    private static FixtureShape key(souther.compiler.check.BoundaryMapKey key) {
        return switch (key.representation()) {
            case MapKeyRepresentation.Lexical l -> new Scalar(l.leaf());
            case MapKeyRepresentation.NamedKey n -> new Nominal(n.name());
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
        LeafScalar scalar = LeafScalar.of(prim);
        if (scalar == null) {
            throw new FixtureException("`Raw` is the reserved type and has no decoder, so a fixture"
                    + " has nothing to build one through");
        }
        return new Scalar(scalar);
    }

    /**
     * A name a fixture builds through the codec derived for it.
     *
     * <p>Which names have one is what {@link Symbols#declaredByCompilation} answers: a codec is
     * derived for what a module of this compilation declared, and for nothing else. The language's
     * own vocabulary is the other side of that line — a rounding mode is implemented by
     * souther-runtime and belongs to no compiled module, so nothing derived one for it, and a
     * rounding policy is a computation's input rather than a value read from text anyway.
     *
     * <p>Asked of that answer rather than worked out from where the name lives. Reading it off the
     * runtime namespace and a failed lookup computes the same set out of a spelling convention and
     * an absence, which is two things to keep true where the table already holds one.
     *
     * <p>{@code Raw} is spelled like a primitive and denotes a reference, which is the whole reason
     * the reader's {@code Raw} arm never ran — it fell through to reflection and failed there
     * instead. It is refused as the reserved name it is.
     */
    private static FixtureShape nominal(TypeName name, Symbols symbols) {
        if (name.isPrimitive()) {
            return scalar(primitive(name));
        }
        if (!symbols.declaredByCompilation(name)) {
            throw new FixtureException("`" + name.name() + "` is declared by the language rather"
                    + " than by a module here, so no codec was derived for it and a fixture has"
                    + " nothing to build one through");
        }
        return new Nominal(name);
    }

    /** The primitive a primitive-spelled name denotes, read through the inverse of the mint one is
     *  made by. {@code Raw} answers a primitive and is refused as the reserved name it is; a
     *  primitive-module name that denotes none — {@code Some}, {@code None} — answers nothing. */
    private static Type.Prim primitive(TypeName name) {
        Type.Prim prim = name.primitiveKind();
        if (prim == null) {
            throw new FixtureException("`" + name.name() + "` is not a type this example can read");
        }
        return prim;
    }
}
