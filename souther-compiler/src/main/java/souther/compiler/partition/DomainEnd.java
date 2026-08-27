package souther.compiler.partition;

import souther.compiler.check.MatchedEndAttribution;
import souther.compiler.numeric.EndSide;

/**
 * Where the rules leave a quantity off on one side, and which declarations took it in there.
 *
 * <p>The place is what a run stopping there is owed for: it is what every rule about the position
 * leaves together, and no one of them is the reason. Which declarations moved it is a different
 * question and is answered here beside the place rather than inside it — a run stopping at the same
 * value is the same thing to write a row for however the position came to stop there, and two
 * readings that disagree about who narrowed it are still one point.
 *
 * <p>Both travel together because both are known where the position was read, and the day they are
 * carried apart is the day something has to put them back together by what they have in common —
 * which is the value, and reading the declarations back off a value is what this exists to avoid.
 *
 * <p><b>Which of the two ends this is, travels too.</b> A quantity holding one value stops there
 * both ways, so the two ends can lower to one {@link Bound} — and told apart by the place alone,
 * what was worked out at one end can be written down beside the other. The side is carried from
 * where the end was read rather than recovered here: the comparison a run makes against this
 * ({@link QuantityArrangement}) asks whether the run stops at this place, which is a different
 * question and answers nothing about which end it is.
 *
 * <p>The attribution is kept as it came from the reading, unopened. A name is made bare where the
 * point is settled and not before, so an end the run turns out not to stop at costs nothing to have
 * carried.
 */
public final class DomainEnd {

    private final EndSide side;
    private final Bound bound;
    private final MatchedEndAttribution attribution;

    private DomainEnd(EndSide side, Bound bound, MatchedEndAttribution attribution) {
        if (side == null || bound == null) {
            throw new IllegalArgumentException("an end the rules leave is one of the two, somewhere");
        }
        this.side = side;
        this.bound = bound;
        this.attribution = attribution;
    }

    /**
     * An end the reading holding {@code attribution} was asked about and answered for, lowered onto
     * the value the quantity takes.
     *
     * <p>The attribution comes from a reading that was asked about this very end, so nothing here
     * has to decide whether the names belong to it. What is added is the lowering, which is why this
     * is the only way one of these is built with names: the {@link Bound} and the {@link
     * souther.compiler.numeric.Endpoint} the names were matched against are two layers' answers
     * about one end, and a caller free to pair them would be pairing them by the number again.
     */
    static DomainEnd at(EndSide side, Bound bound, MatchedEndAttribution attribution) {
        return bound == null ? null : new DomainEnd(side, bound, attribution);
    }

    /** An end nothing took in, which is what a position no declaration relates to anything has. */
    static DomainEnd at(EndSide side, Bound bound) {
        return at(side, bound, null);
    }

    /** Which of the quantity's two ends this is. */
    public EndSide side() {
        return side;
    }

    /** Where the rules leave off. */
    public Bound bound() {
        return bound;
    }

    /** What took the end in, or null where nothing did — the reading answered about another end, or
     *  about none. */
    MatchedEndAttribution attribution() {
        return attribution;
    }

    /** Where {@code end} is, or null where there is no end that way. */
    public static Bound boundOf(DomainEnd end) {
        return end == null ? null : end.bound();
    }
}
