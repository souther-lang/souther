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
 * <p>The set closed here is the representations a reader branches on, not the types a key may be
 * written as. Another {@code data CustomerId = String} is a {@link Newtype} over {@link Text} and
 * moves nothing. A representation that does not yet exist is a new case, and every reader that acts
 * on a representation stops compiling until it says what to do with it — while a reader that only
 * wraps and unwraps a named key is left alone, because that distinction is not the one that changed.
 */
public sealed interface BoundaryMapKey {

    /** The type in the language a key of this representation has — what the map it keys is a map of.
     *  Answered per case rather than by switching, so a case added here cannot forget it. */
    Type type();

    /** A bare string: {@code String} itself, and what a String-backed newtype is admitted through. */
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

    /**
     * A newtype key: the type to construct and unwrap, and the representation the value inside it
     * crosses as. The two are separate because different readers need different halves — the codec
     * wraps and unwraps by name, and only the text conversion depends on {@code representation}.
     */
    record Newtype(TypeName name, BoundaryMapKey representation) implements BoundaryMapKey {
        @Override
        public Type type() {
            return Type.ref(name);
        }
    }

    /** A sum every case of which is a unit data: it crosses as the case's name, a bare string
     *  (issue #161). Not a {@link Newtype}: it is built from and rendered to that name rather than
     *  wrapping a value, which is a difference the encoder's call site branches on. */
    record UnitEnum(TypeName name) implements BoundaryMapKey {
        @Override
        public Type type() {
            return Type.ref(name);
        }
    }
}
