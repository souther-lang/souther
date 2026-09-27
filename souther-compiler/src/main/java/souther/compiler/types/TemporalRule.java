package souther.compiler.types;

import java.util.List;
import java.util.Optional;
import souther.temporal.TemporalText;
import souther.temporal.TemporalText.Kind;
import souther.temporal.TemporalText.Refusal;

/**
 * What a temporal has to satisfy to become a value, said once for every reader of it.
 *
 * <p>The rules are the type's and not the path's. A {@code Time} holds no fraction of a second
 * wherever it arrives, and text naming a leap second is no {@code Instant} wherever it arrives
 * (spec §a-local-temporal-is-held-to-the-second, §a-leap-second-is-no-moment). Which text is a
 * temporal at all is the language's, and {@link TemporalText} states it; this table says which of
 * its questions a decoder asks of the text before a parser sees it, and in what order, so that
 * the parser only builds the value.
 *
 * <p>The places that build a decoder read the table. Two of them do: {@code CodecGen} emits the
 * calls into a generated class, and {@code Runner} makes them in Java. Neither may state a rule of
 * its own, and a temporal added here is one both have to answer for.
 *
 * <p>The parse the two call to build the value is not in the table. {@code CodecGen} names a method
 * to emit and {@code Runner} switches over {@link LeafScalar}, and each is exhaustive, so a temporal
 * added here stops both builds.
 *
 * @param text        the questions asked of the text, in order; the first that fails is the reason
 * @param guardsValue whether the parsed value is held to the second, for a caller that hands over a
 *                    real temporal and so has no text to ask
 */
public record TemporalRule(List<TextGate> text, boolean guardsValue) {

    /**
     * One question asked of the text: whether it is a {@code kind}, or, with {@code only}, whether
     * that is not the reason it is refused for.
     *
     * @param message what a refusal says the text does
     */
    public record TextGate(Kind kind, Optional<Refusal> only, String message) {

        /** The question, for a caller that is Java. */
        public boolean holds(Object input) {
            return TemporalText.holds(input, kind, only);
        }
    }

    /** Raoh's code for text whose shape is wrong, which is what every refusal is a kind of. */
    public static final String REFUSED = "invalid_format";

    public static final String SUB_SECOND = TemporalText.says(Kind.TIME, Refusal.SUB_SECOND);

    public static final String LEAP_SECOND = TemporalText.says(Kind.INSTANT, Refusal.LEAP_SECOND);

    /**
     * The rule for a temporal, or null where the primitive is not one.
     *
     * <p>A {@code Time} and a {@code DateTime} refuse a fraction first, so that {@code 09:30:00.000}
     * is told it carries one and not that it is malformed, and are then held to the form. An
     * {@code Instant} refuses a leap second first for the same reason. The value is held to the
     * second as well, which is where a fraction reaches a caller that hands over a real
     * {@code LocalTime}.
     */
    public static TemporalRule of(Type.Prim prim) {
        return switch (prim) {
            case DATE -> new TemporalRule(List.of(form(Kind.DATE)), false);
            case TIME -> new TemporalRule(List.of(not(Kind.TIME, Refusal.SUB_SECOND), form(Kind.TIME)),
                    true);
            case DATETIME -> new TemporalRule(List.of(
                    not(Kind.DATETIME, Refusal.SUB_SECOND), form(Kind.DATETIME)),
                    true);
            case INSTANT -> new TemporalRule(List.of(
                    not(Kind.INSTANT, Refusal.LEAP_SECOND), form(Kind.INSTANT)),
                    false);
            case INT, STRING, BOOL, DECIMAL, RATIONAL -> null;
        };
    }

    private static TextGate form(Kind kind) {
        return new TextGate(kind, Optional.empty(), TemporalText.says(kind, Refusal.MALFORMED));
    }

    private static TextGate not(Kind kind, Refusal reason) {
        return new TextGate(kind, Optional.of(reason), TemporalText.says(kind, reason));
    }

    /** The rule for a leaf scalar, or null where it is not a temporal. */
    public static TemporalRule of(LeafScalar scalar) {
        return of(scalar.type());
    }
}
