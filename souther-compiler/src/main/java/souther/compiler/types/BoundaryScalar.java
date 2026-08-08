package souther.compiler.types;

/**
 * A scalar the boundary writes as itself. The set is closed here rather than being the primitives
 * minus one: {@code Raw} is spelled like a primitive and is not a scalar anything may carry, so a
 * witness built out of {@link Type.Prim} would hold a value the boundary refuses and leave every
 * reader with an arm for it.
 *
 * <p>{@link #of} is the one way in, and it answers nothing for {@code Raw}. What comes out is a
 * value a decoder and an encoder are both built for.
 */
public enum BoundaryScalar {

    STRING(Type.Prim.STRING),
    INT(Type.Prim.INT),
    BOOL(Type.Prim.BOOL),
    DECIMAL(Type.Prim.DECIMAL),
    DATE(Type.Prim.DATE),
    DATETIME(Type.Prim.DATETIME);

    private final Type.Prim prim;

    BoundaryScalar(Type.Prim prim) {
        this.prim = prim;
    }

    /** The type in the language this scalar stands for. */
    public Type.Prim type() {
        return prim;
    }

    /** The scalar {@code prim} is, or null when it is not one — which only {@code Raw} is not. */
    public static BoundaryScalar of(Type.Prim prim) {
        return switch (prim) {
            case STRING -> STRING;
            case INT -> INT;
            case BOOL -> BOOL;
            case DECIMAL -> DECIMAL;
            case DATE -> DATE;
            case DATETIME -> DATETIME;
            case RAW -> null;
        };
    }
}
