package souther.compiler.types;

/**
 * Where a construction standing in a body came from — what a permission check needs in order to tell
 * a construction the body makes from one that arrived in it already made.
 *
 * <p>Expansion is why the question has to be answered at all. A value is substituted at each
 * reference and a published body is spliced into its reader, so a construction written somewhere
 * else ends up as the same node one written here would be. Asking the node is the only way left.
 *
 * <p>The two ways in are recorded apart because they are not answered alike. A published body names
 * the module that published it, and that module hands over only what it declares: a construction of
 * a third module's type is nobody's to hand over, so the module is compared against the type's. A
 * value reference names no module — the construction belongs to the definition of the value, and the
 * behavior reading the name originates nothing whatever module declared the type.
 */
public record ConstructionOrigin(String publishedBy, boolean viaValueReference) {

    private static final ConstructionOrigin OWN = new ConstructionOrigin(null, false);

    /** A construction written where it stands. */
    public static ConstructionOrigin own() {
        return OWN;
    }

    /** The same construction, carried into a reader by {@code module}'s published body. */
    public ConstructionOrigin publishedIn(String module) {
        return new ConstructionOrigin(module, viaValueReference);
    }

    /** The same construction, carried into a body by a value that body named. */
    public ConstructionOrigin carriedByValue() {
        return new ConstructionOrigin(publishedBy, true);
    }

    /**
     * Whether the body holding this construction of {@code built} was handed it rather than making
     * it, and so answers for none of it.
     */
    public boolean carried(TypeSymbol built) {
        return viaValueReference || (publishedBy != null && publishedBy.equals(built.module()));
    }
}
