package souther.compiler.types;

/**
 * How a {@code Map} key is written as text. A map's external form is a JSON object, whose keys are
 * strings, so a key that has a representation at all both renders as and parses from a bare string —
 * and which string is what this names (ADR-0040).
 *
 * <p>This is a classification of a type, and describing one is not admitting one. A key position may
 * be established by a behavior's boundary, by a data's field, or by a fixture, and each decides for
 * itself what it will take — so the question "what would this key convert through" is answered here,
 * and the question "is this key allowed here" is answered by the position. The second is what a
 * {@link souther.compiler.check.CrossingMapKey} says, and it is made from one of these rather than
 * instead of it.
 *
 * <p>Two cases, because a reader has two things to do. A {@link Lexical} key is a primitive, written
 * as the leaf's own form and read back through it. A {@link NamedKey} is a type a model declared,
 * written by that type's derived {@code encoder()} and read by its {@code decoder()} — which carry
 * the conversion and the invariant — so the reader names the type and the codec does the rest.
 *
 * <p>Nothing here says what a named key is made of. Which types may be keys is settled before this
 * is built: a newtype is one exactly when what it wraps is one, and
 * {@link souther.compiler.check.TypeOps#classifyConcreteMapKey} answers that by unwrapping. What
 * comes out is the outermost name, because that is whose codec runs. So a wrapper over a base
 * already admitted needs no case of its own and no reader branch: a newtype over a temporal, over
 * an enumeration, or over another newtype arrives as the same {@link NamedKey} a newtype over
 * {@code String} does.
 *
 * <p>That is the one axis this is open on, and the other is closed on purpose. A new primitive key
 * is not admitted by anything here — the classifier answers for each primitive by name and
 * {@link Lexical} lists the ones there are — so a primitive that rendered as a bare string without
 * being a temporal would be a case here and a branch where a key is decoded. What that buys is that
 * a type does not key a map merely for having a leaf codec, which {@code Int} and {@code Decimal}
 * have.
 */
public sealed interface MapKeyRepresentation {

    /** The type in the language a key of this representation has — what the map it keys is a map of. */
    Type type();

    /**
     * A primitive key, written as the leaf's own text. Closed at the text and the four temporals: a
     * JSON object's key is a string, and {@code Int}, {@code Bool} and {@code Decimal} are written
     * as themselves elsewhere, so admitting one here would make a type's external form depend on
     * where it stands.
     */
    sealed interface Lexical extends MapKeyRepresentation {

        /** The leaf the key is written through and read back by. */
        LeafScalar leaf();

        @Override
        default Type type() {
            return leaf().type();
        }
    }

    /** A bare string, {@code String} itself. */
    record Text() implements Lexical {
        @Override
        public LeafScalar leaf() {
            return LeafScalar.STRING;
        }
    }

    /** A {@code Date}, as the ISO form a date field already crosses with. */
    record Date() implements Lexical {
        @Override
        public LeafScalar leaf() {
            return LeafScalar.DATE;
        }
    }

    /** A {@code Time}, as its ISO form. */
    record Time() implements Lexical {
        @Override
        public LeafScalar leaf() {
            return LeafScalar.TIME;
        }
    }

    /** A {@code DateTime}, as its ISO form. */
    record DateTime() implements Lexical {
        @Override
        public LeafScalar leaf() {
            return LeafScalar.DATETIME;
        }
    }

    /** An {@code Instant}, as its ISO form. */
    record Instant() implements Lexical {
        @Override
        public LeafScalar leaf() {
            return LeafScalar.INSTANT;
        }
    }

    /**
     * A type a model declared: a newtype over anything that is itself a key, or an enumeration — a
     * sum every case of which is a unit data, which crosses as that case's name (issue #161).
     *
     * <p>Both go through the named type's own codec, so what it wraps does not reach here. A
     * {@code data ProductId = String} writes its bare value, a {@code data LoanDate = Date} writes
     * the ISO form its base writes, and an enumeration writes its case's name — each because that is
     * what its derived {@code encoder()} does, and each read back by the {@code decoder()} that
     * inverts it.
     */
    record NamedKey(TypeSymbol name) implements MapKeyRepresentation {
        @Override
        public Type type() {
            return Type.ref(name);
        }
    }
}
