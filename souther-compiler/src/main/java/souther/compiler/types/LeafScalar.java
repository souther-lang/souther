package souther.compiler.types;

/**
 * A primitive a derived codec reads and writes as itself.
 *
 * <p>The set is closed here rather than being the primitives minus one. {@code Raw} is spelled like
 * a primitive and is not a scalar anything carries: no leaf codec exists for it, so a witness built
 * out of {@link Type.Prim} would hold a value every reader below then needs an arm for. {@link #of}
 * is the one way in, and it answers nothing for {@code Raw}.
 *
 * <p>One type for one fact, read by two questions that are not the same question. What a behavior's
 * boundary writes as itself is one; what a fixture can be decoded into is another. They list the
 * same primitives because both are asking which ones a codec exists for — so that is what this says,
 * once. Written twice, agreeing today would be the whole of the guarantee, and the day another is
 * admitted or one is taken away only one of them would move.
 */
public enum LeafScalar {

    STRING(Type.Prim.STRING),
    INT(Type.Prim.INT),
    BOOL(Type.Prim.BOOL),
    DECIMAL(Type.Prim.DECIMAL),
    DATE(Type.Prim.DATE),
    TIME(Type.Prim.TIME),
    DATETIME(Type.Prim.DATETIME),
    INSTANT(Type.Prim.INSTANT);

    private final Type.Prim prim;

    LeafScalar(Type.Prim prim) {
        this.prim = prim;
    }

    /** The type in the language this scalar stands for. */
    public Type.Prim type() {
        return prim;
    }

    /** The scalar {@code prim} is, or null when it is not one — which only {@code Raw} is not. */
    public static LeafScalar of(Type.Prim prim) {
        return switch (prim) {
            case STRING -> STRING;
            case INT -> INT;
            case BOOL -> BOOL;
            case DECIMAL -> DECIMAL;
            case DATE -> DATE;
            case TIME -> TIME;
            case DATETIME -> DATETIME;
            case INSTANT -> INSTANT;
            case RAW -> null;
        };
    }
}
