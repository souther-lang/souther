package souther.compiler.types;

/**
 * What a {@code Map} key admitted at the boundary is converted through. A map's external form is a
 * JSON object, whose keys are strings, so an admitted key both renders as and parses from a bare
 * string — and which string is what this names (ADR-0040).
 *
 * <p>It is a witness rather than a yes. Admitting a key establishes a fact about it, and a reader
 * that has to build a decoder, render an encoder's keys or lower the key into the codec IR needs
 * that fact; before this, each worked it out again from whatever representation it held, and the
 * checker's own rule was read a second time in the backend.
 *
 * <p>The cases are flat, and {@link StringNewtype} names the base it wraps rather than holding it.
 * A nested case — a newtype carrying its representation inside it — would be a witness no reader
 * reads: a named key is decoded by that type's own generated {@code decoder()}, which has the
 * conversion and the invariant inside it, and encoded through a {@code value()} accessor typed
 * {@code () -> String}. Both hold of a String-backed newtype and of nothing else, so the base
 * belongs in the case's name, where admitting a newtype over another base is a new case and every
 * reader is asked what to do with it. Nested, the same widening would leave the newtype arm
 * untouched and compiling.
 *
 * <p>What the set closes over is that: the representations a reader branches on, not the types a key
 * may be written as. Another {@code data CustomerId = String} is a {@link StringNewtype} and moves
 * nothing.
 */
public sealed interface BoundaryMapKey {

    /** The type in the language a key of this representation has — what the map it keys is a map of.
     *  Answered per case rather than by switching, so a case added here cannot forget it. */
    Type type();

    /** A bare string, {@code String} itself. */
    record Text() implements BoundaryMapKey {
        @Override
        public Type type() {
            return Type.STRING;
        }
    }

    /** A {@code Date}, as the ISO form a date field already crosses with. */
    record Date() implements BoundaryMapKey {
        @Override
        public Type type() {
            return Type.DATE;
        }
    }

    /** A {@code DateTime}, as its ISO form. */
    record DateTime() implements BoundaryMapKey {
        @Override
        public Type type() {
            return Type.DATETIME;
        }
    }

    /** A newtype over {@code String} ({@code data X = String}): built by its own decoder, which
     *  applies its invariant, and rendered by its {@code value()}, which is the bare string. Both
     *  hold because the base is text, which is why the base is in the name. */
    record StringNewtype(TypeName name) implements BoundaryMapKey {
        @Override
        public Type type() {
            return Type.ref(name);
        }
    }

    /** A sum every case of which is a unit data: it crosses as the case's name, a bare string
     *  (issue #161). Not a {@link StringNewtype}: it is built from and rendered to that name rather
     *  than wrapping a value, which is a difference the encoder's call site branches on. */
    record UnitEnum(TypeName name) implements BoundaryMapKey {
        @Override
        public Type type() {
            return Type.ref(name);
        }
    }
}
