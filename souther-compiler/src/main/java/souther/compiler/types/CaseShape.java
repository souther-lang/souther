package souther.compiler.types;

/**
 * What membership in a sum adds to a case's own representation (spec 11.2). A derived codec is the
 * standalone representation of a type; where that type stands as a case, the sum's encoding puts the
 * discriminator on it, and this is the shape of that operation.
 *
 * <p>Read from the declaration — braces, {@code = Y}, or no contents at all — and not from what the
 * derived codec came out as. A newtype over a record writes an object and is still wrapped, so
 * "writes an object" and "the discriminator can go in it" are different questions; asking the second
 * through the first is what left the envelope with two owners.
 */
public enum CaseShape {

    /** A braced data: its fields lie beside the discriminator, in the case's own object. */
    PRODUCT,

    /** A data with no contents: the discriminator alone. */
    UNIT,

    /** A newtype, or a primitive standing as a member of a behavior's answer: the standalone
     *  representation under {@code "value"}, beside the discriminator. */
    WRAPPED;

    /** The key a wrapped case's contents are written under. */
    public static final String ENVELOPE_KEY = "value";
}
