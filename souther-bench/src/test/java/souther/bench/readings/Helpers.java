package souther.bench.readings;

/**
 * Places outside the stage that read raw structure and answer with a word.
 *
 * <p>Neither owns a question: each is the reading of something the model already says, given
 * another name and a smaller return type. They are here because that is exactly what a walk over
 * return types cannot see — what is followed has to be the call.
 */
public final class Helpers {

    private Helpers() {}

    /** Whether the name declares a record, which is what reaching the declaration answers. */
    public static boolean isARecord(Written.Names names, String name) {
        return names.declaredNode(name) instanceof Written.Declared.Record;
    }

    /** Whether the compound holds a leaf, which is what taking it apart answers. */
    public static boolean holdsALeaf(Written.Position position) {
        return position instanceof Written.Position.Built.OfOne one
                && one.element() instanceof Written.Position.Leaf;
    }
}
