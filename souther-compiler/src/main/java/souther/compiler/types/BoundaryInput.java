package souther.compiler.types;

/**
 * A type a value can arrive as, at a behavior's boundary. Every case is a shape a decoder is built
 * for, so a reader that switches over this is total over what can arrive and has no arm for anything
 * else.
 *
 * <p>Which types those are is decided where the boundary's obligations are checked, and this is the
 * answer travelling rather than the question being asked again. A {@link Type} is the whole type
 * language: a tuple, a function, an optional, an anonymous union and a name the language keeps for
 * itself are all writable, and each is refused by the obligation that owns it. A reader handed a
 * {@code Type} can only know that by knowing all of them; a reader handed one of these knows it by
 * having one.
 *
 * <p>There is no case for an anonymous union. A parameter names a single type, so an input cannot be
 * one — which is why an input and an output are separate types here rather than one with an arm each
 * reader has to answer for.
 */
public sealed interface BoundaryInput {

    /** The type in the language this shape stands for. Answered per case rather than by switching, so
     *  a case added here cannot forget it. */
    Type type();

    /** A scalar the boundary writes as itself. */
    record Scalar(LeafScalar scalar) implements BoundaryInput {
        @Override
        public Type type() {
            return scalar.type();
        }
    }

    /** A type a model declared, decoded by the codec derived for it. */
    record Nominal(TypeName name) implements BoundaryInput {
        @Override
        public Type type() {
            return Type.ref(name);
        }
    }

    /** A list of them. */
    record ListOf(BoundaryInput element) implements BoundaryInput {
        @Override
        public Type type() {
            return Type.list(element.type());
        }
    }

    /** A set of them. */
    record SetOf(BoundaryInput element) implements BoundaryInput {
        @Override
        public Type type() {
            return Type.set(element.type());
        }
    }

    /** A map of them, under a key the boundary can write as text. The key is the witness the map-key
     *  rule already answers with, so a key position cannot hold a list or an option. */
    record MapOf(BoundaryMapKey key, BoundaryInput value) implements BoundaryInput {
        @Override
        public Type type() {
            return Type.map(key.type(), value.type());
        }
    }
}
