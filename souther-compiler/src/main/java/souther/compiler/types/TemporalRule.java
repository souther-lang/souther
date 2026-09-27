package souther.compiler.types;

import souther.temporal.TemporalText;
import souther.temporal.TemporalText.Kind;
import souther.temporal.TemporalText.Refusal;

/**
 * What a temporal's value has to satisfy once it is built, said once for every reader of it.
 *
 * <p>Which text is a temporal at all is not here. That is the language's, {@link TemporalText}
 * states it (spec §temporal-text), and every path a text arrives by asks it before a parser sees
 * the text, so the parser only builds the value. What is left is a rule about the value: a
 * {@code Time} and a {@code DateTime} hold no fraction of a second wherever they come from
 * (spec §a-local-temporal-is-held-to-the-second), including a value a Java caller hands over
 * already built, which has no text to ask.
 *
 * <p>Two places build a decoder and read this: {@code CodecGen} emits the calls into a generated
 * class, and {@code JsonBoundary} makes them in Java for the runner. Neither may state a rule of
 * its own, and a temporal added here is one both have to answer for. The parse each calls to build
 * the value is not here: {@code CodecGen} names a method to emit and {@code JsonBoundary} switches
 * over {@link LeafScalar}, and each is exhaustive, so a temporal added here stops both builds.
 *
 * @param guardsValue whether the built value is held to the second
 */
public record TemporalRule(boolean guardsValue) {

    /** Raoh's code for text whose shape is wrong, which is what every refusal of a text is a kind of. */
    public static final String REFUSED = "invalid_format";

    /** What a value with a fraction of a second says, worded as the text that carries one is. */
    public static final String SUB_SECOND = TemporalText.says(Kind.TIME, Refusal.SUB_SECOND);

    /**
     * The rule for a temporal, or null where the primitive is not one.
     *
     * <p>A {@code Date} has no time of day to carry a fraction. An {@code Instant} is the temporal
     * that keeps a sub-second reading.
     */
    public static TemporalRule of(Type.Prim prim) {
        return switch (prim) {
            case DATE, INSTANT -> new TemporalRule(false);
            case TIME, DATETIME -> new TemporalRule(true);
            case INT, STRING, BOOL, DECIMAL, RATIONAL -> null;
        };
    }

    /** The rule for a leaf scalar, or null where it is not a temporal. */
    public static TemporalRule of(LeafScalar scalar) {
        return of(scalar.type());
    }
}
