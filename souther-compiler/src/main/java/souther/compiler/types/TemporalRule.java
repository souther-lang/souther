package souther.compiler.types;

/**
 * What a temporal's text has to satisfy to become a value, said once for every reader of it.
 *
 * <p>The rules are the type's and not the path's. A {@code Time} holds no fraction of a second
 * wherever it arrives, and text naming a leap second is no {@code Instant} wherever it arrives
 * (spec §a-local-temporal-is-held-to-the-second, §a-leap-second-is-no-moment). Both were written at
 * the place a decoder happened to be built instead, and both went missing on a path that built one
 * somewhere else: a map key spelled its own parse and took a fraction the same type refused at a
 * field, and the runner's own decoders — the ones {@code souther run} reads a top-level argument
 * with — took every text the generated ones refuse.
 *
 * <p>So the policy is a table and the places that build a decoder read it. Two of them do:
 * {@code CodecGen} emits the calls into a generated class, and {@code Runner} makes them in Java.
 * Neither may state a rule of its own, and a temporal added here is one both have to answer for.
 *
 * <p>What the table does <em>not</em> carry across both is which parse to call. {@link #factory} is a
 * method name, which is what an emitter needs and what a Java caller cannot use without reflection —
 * so {@code Runner} switches over {@link LeafScalar} to reach {@code date()} / {@code time()} and
 * their siblings, each of which answers a different type. That switch is exhaustive, so a temporal
 * added here stops that build too; what is shared is the part that went wrong, which was never which
 * parse ran but which refusals were chained around it.
 *
 * @param factory     the Raoh leaf the text is parsed by
 * @param guardsText  whether the text is refused before the parse, for what the parse would fold
 * @param guardsValue whether the parsed value is held to the second
 */
public record TemporalRule(String factory, boolean guardsText, boolean guardsValue) {

    /** Raoh's code for text whose shape is wrong, which is what both refusals are a kind of. */
    public static final String REFUSED = "invalid_format";

    public static final String SUB_SECOND = "holds no fraction of a second";

    public static final String LEAP_SECOND = "names a leap second, which is no moment here";

    /**
     * The rule for a temporal, or null where the primitive is not one.
     *
     * <p>A {@code Date} has no time of day to carry a fraction and no second to be the wrong one.
     * A {@code Time} and a {@code DateTime} are held to the second after the parse, which is where
     * a fraction of one becomes visible. An {@code Instant} is guarded before it: {@code
     * Instant.parse} reads {@code 23:59:60} as {@code 23:59:59}, so afterwards the substitution is
     * gone and only the text still says which second was named.
     */
    public static TemporalRule of(Type.Prim prim) {
        return switch (prim) {
            case DATE -> new TemporalRule("date", false, false);
            case TIME -> new TemporalRule("time", false, true);
            case DATETIME -> new TemporalRule("dateTime", false, true);
            case INSTANT -> new TemporalRule("iso8601", true, false);
            case INT, STRING, BOOL, DECIMAL, RAW -> null;
        };
    }

    /** The rule for a leaf scalar, or null where it is not a temporal. */
    public static TemporalRule of(LeafScalar scalar) {
        return of(scalar.type());
    }
}
