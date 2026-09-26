package souther.compiler.types;

/**
 * How a decoder says that what it read is not text, said once for every place that builds one.
 *
 * <p>Whether it is text is not decided here. {@code Strings.admitted} decides that for every door
 * text comes in by, and answers null for text holding half of a surrogate pair; a decoder reads that
 * null as a failure at its path, and this is the failure. Two places build decoders — {@code
 * CodecGen} into a generated class and {@code JsonBoundary} in Java — and both report the same code
 * and message, so a value refused by one is refused the same way by the other.
 */
public final class TextRule {

    private TextRule() {}

    /** Raoh's code for text whose shape is wrong, the one a temporal's text is refused with too
     *  ({@link TemporalRule#REFUSED}): what arrived is a string, and its content is not a sequence
     *  of Unicode scalar values. A value that is not a string at all is Raoh's
     *  {@code type_mismatch}, and this is not that. */
    public static final String REFUSED = "invalid_format";

    public static final String HALF_A_PAIR =
            "holds half of a surrogate pair, which is not a character";
}
