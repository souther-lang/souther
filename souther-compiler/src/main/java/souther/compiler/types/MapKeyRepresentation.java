package souther.compiler.types;

/**
 * What a {@code Map} key is converted through. A map's external form is a JSON object, whose keys are
 * strings, so a key that has a representation at all both renders as and parses from a bare string —
 * and which string is what this names (ADR-0040).
 *
 * <p>This is a classification of a type, and describing one is not admitting one. A key position may
 * be established by a behavior's boundary, by a data's field, or by a fixture, and each decides for
 * itself what it will take — so the question "what would this key convert through" is answered here,
 * and the question "is this key allowed here" is answered by the position. The second is what a
 * {@link souther.compiler.check.BoundaryMapKey} says, and it is made from one of these rather than
 * instead of it.
 *
 * <p>The cases are flat, and {@link StringNewtype} names the base it wraps rather than holding it.
 * A nested case — a newtype carrying its representation inside it — would be a distinction no reader
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
public sealed interface MapKeyRepresentation {

    /** The type in the language a key of this representation has — what the map it keys is a map of.
     *  Answered per case rather than by switching, so a case added here cannot forget it. */
    Type type();

    /** A bare string, {@code String} itself. */
    record Text() implements MapKeyRepresentation {
        @Override
        public Type type() {
            return Type.STRING;
        }
    }

    /** A {@code Date}, as the ISO form a date field already crosses with. */
    record Date() implements MapKeyRepresentation {
        @Override
        public Type type() {
            return Type.DATE;
        }
    }

    /** A {@code DateTime}, as its ISO form. */
    record DateTime() implements MapKeyRepresentation {
        @Override
        public Type type() {
            return Type.DATETIME;
        }
    }

    /** A newtype over {@code String} ({@code data X = String}): built by its own decoder, which
     *  applies its invariant, and rendered by its {@code value()}, which is the bare string. Both
     *  hold because the base is text, which is why the base is in the name. */
    record StringNewtype(TypeName name) implements MapKeyRepresentation {
        @Override
        public Type type() {
            return Type.ref(name);
        }
    }

    /** A sum every case of which is a unit data: it crosses as the case's name, a bare string
     *  (issue #161). Not a {@link StringNewtype}: it is built from and rendered to that name rather
     *  than wrapping a value, which is a difference the encoder's call site branches on. */
    record UnitEnum(TypeName name) implements MapKeyRepresentation {
        @Override
        public Type type() {
            return Type.ref(name);
        }
    }
}
