package souther.compiler.numeric;

/**
 * Which way along an order something runs from where it starts.
 *
 * <p>Shared rather than owned by any one of the things that needs it, and here because every one of
 * them is about an order: which way a run of values lies, which end of a range a value is wanted
 * near, which side of a threshold a rule is satisfied on, and which way a place is rounded.
 *
 * <p>It belonged to the first of those to be written, and the others named it through that one — so
 * a carrier, which is the thing that actually knows how its own values run, could not be asked a
 * question with a direction in it. What that cost was a second answer: which end of a range a row
 * should come from was said once where levels are chosen and again, differently, where a place is,
 * and only one of the two said it on purpose.
 */
public enum Towards {
    ABOVE,
    BELOW;

    /** The other way. */
    public Towards opposite() {
        return this == ABOVE ? BELOW : ABOVE;
    }
}
