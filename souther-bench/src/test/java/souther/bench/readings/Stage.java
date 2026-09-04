package souther.bench.readings;

/**
 * A stage written to be read: every shape the walk has to tell apart, and one of nothing at all.
 *
 * <p>Each method here is a claim about the walk rather than about this compiler. What they have in
 * common is that a reader looking at the source can see which answer is right, so a walk that gives
 * another has been caught by something that does not depend on the compiler standing still.
 */
public final class Stage {

    private Stage() {}

    /** Reaches a declaration itself, which is the plainest reading there is. */
    public static boolean readsADeclaration(Written.Names names, String name) {
        return names.declaredNode(name) instanceof Written.Declared.Record record
                && record.holdsAnything();
    }

    /** Takes a compound apart, which is the other. */
    public static Written.Position takesACompoundApart(Written.Position position) {
        return position instanceof Written.Position.Built.OfOne one ? one.element() : null;
    }

    /**
     * Takes apart a compound whose component holds many, which no descriptor says.
     *
     * <p>Beside the one above because the two are read differently: what that one holds is written
     * in the descriptor of its component, and what this one holds is written only in the generic
     * signature. A reading of components that looked at descriptors alone would see this one hold
     * nothing, and taking it apart would read as taking nothing apart.
     */
    public static Written.Position takesApartOneHoldingMany(Written.Position position) {
        return position instanceof Written.Position.Built.OfMany many
                ? many.elements().getFirst() : null;
    }

    /**
     * Asks which compound it is and takes nothing out, which is a reading all the same.
     *
     * <p>Beside the one above and not the same shape. That one asks and then reads a component, so
     * a walk seeing only the component would still see it; this one asks and stops, which is what
     * telling a list from a map is — and a reader with the answer has divided the position without
     * anything having handed it a division.
     */
    public static boolean asksWhichCompoundItIs(Written.Position position) {
        return position instanceof Written.Position.Built.OfTwo;
    }

    /** Reaches a declaration two calls away, behind something that answers with a word. */
    public static boolean readsThroughAHelper(Written.Names names, String name) {
        return Helpers.isARecord(names, name);
    }

    /** Takes a compound apart from behind a helper that hands back no type of anybody's. */
    public static boolean takesOneApartThroughAHelper(Written.Position position) {
        return Helpers.holdsALeaf(position);
    }

    /** Reaches a reading past a boundary the walk is told to go through. */
    public static boolean readsPastATransparentBoundary(Written.Names names, String name) {
        return Transparent.answering(names, name);
    }

    /** Asks an authority, which answers and hands nothing raw back. */
    public static String asksAnAuthority(Written.Names names, String name) {
        return Opaque.spelling(names, name);
    }

    /** Asks the operation beside it, which answers something else and reaches the declarations. */
    public static boolean asksTheQuestionBesideIt(Written.Names names, String name) {
        return Opaque.somethingElse(names, name);
    }

    /** Reads the name off a leaf, which is a name and not a structure. */
    public static String readsANameOffALeaf(Written.Position position) {
        return position instanceof Written.Position.Leaf leaf ? leaf.name() : null;
    }

    /** Makes a compound, which is not reading one. */
    public static Written.Position makesACompound(Written.Position element) {
        return new Written.Position.Built.OfOne(element);
    }

    /** Reads a component of a compound that holds no position, which reads no structure. */
    public static String readsAComponentHoldingNoPosition(Written.Position.Built.OfTwo pair) {
        return pair.label();
    }
}
