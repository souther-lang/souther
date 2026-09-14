package souther.compiler.partition;

import souther.compiler.check.MatchedEndAttribution;
import souther.compiler.check.NarrowedBounds;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.EndSide;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;

import java.util.Optional;

/**
 * Where the rules leave a quantity off on one side, and which declarations took it in there.
 *
 * <p>The place is what a run stopping there is owed for: it is what every rule about the position
 * leaves together, and no one of them is the reason. Which declarations moved it is a different
 * question and is answered here beside the place rather than inside it — a run stopping at the same
 * value is the same thing to write a row for however the position came to stop there, and two
 * readings that disagree about who narrowed it are still one point.
 *
 * <p><b>Which of the two ends this is, travels too.</b> A quantity holding one value stops there
 * both ways, so the two ends can lower to one {@link Bound} — and told apart by the place alone,
 * what was worked out at one end can be written down beside the other. The comparison a run makes
 * against this ({@link QuantityArrangement}) asks whether the run stops at this place, which is a
 * different question and answers nothing about which end it is.
 *
 * <p><b>One of these with names on it is made in one way and no other.</b> {@link #leaving} picks
 * the end at a side, asks the reading about that end, and lowers that end onto the value the
 * quantity takes — all from the one side it was given. There is no way to hand it a side, a place
 * and an attribution that were arrived at separately, because that is the pairing the whole of this
 * exists to refuse: at a quantity holding one value the two ends lower to one {@code Bound}, and
 * nothing downstream could tell such a pairing from the right one.
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
            throw new IllegalArgumentException(
                    "an end the rules leave is one of the two, somewhere");
        }
        this.side = side;
        this.bound = bound;
        this.attribution = attribution;
    }

    /**
     * Where {@code reach} leaves the quantity on one side, as a value it takes, with whatever
     * {@code narrowed} answers about that very end.
     *
     * <p>Null where the rules leave the quantity everything that way, and where a strict end leaves
     * it no first value past — a run that stops where a rule stops without keeping the place it
     * stops at has no value here for a row to be written at.
     *
     * @param like the level the quantity's places are written as, which says how a number becomes
     *             one of them
     */
    static DomainEnd leaving(LevelSpace space, Level like, NumericDomain.Bounds reach, EndSide side,
                             NarrowedBounds narrowed) {
        Endpoint end = side.at(reach);
        Bound at = valueAt(space, like, end, side);
        return at == null ? null
                : new DomainEnd(side, at, narrowed.matching(side, end).orElse(null));
    }

    /**
     * An end nothing took in, which is what a quantity no declaration relates to anything has.
     *
     * <p>A place and a side and no names, so there is nothing here that could be put beside the
     * wrong end: what the pairing above refuses needs an attribution to make.
     */
    static DomainEnd at(EndSide side, Bound bound) {
        return bound == null ? null : new DomainEnd(side, bound, null);
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

    /** Which end this is and where it leaves off, which is what a message naming one has to say.
     *  The attribution is not here: it is what a reading answered, and a message about the end
     *  reaching somewhere it should not is not about who took it in. */
    @Override
    public String toString() {
        return side + " at " + bound;
    }

    /** Where {@code end} is, or null where there is no end that way. */
    public static Bound boundOf(DomainEnd end) {
        return end == null ? null : end.bound();
    }

    /**
     * The first or last value the rules leave the quantity, from the end they wrote.
     *
     * <p>A value the quantity takes rather than the number a bound carries: a bound the quantity
     * does not stand at leaves the first value it does, and a bound it stands at but does not keep
     * leaves the one beside it.
     */
    private static Bound valueAt(LevelSpace space, Level like, Endpoint end, EndSide side) {
        if (end == null) {
            return null;
        }
        Level at = like instanceof Level.OnACarrier on
                ? new Level.OnACarrier(on.of(), end.at())
                : new Level.ACount(Count.number(end.at()));
        Optional<Level> value = end.inclusive() ? space.nearestAtOrBeyond(at, side.inward())
                : Border.beyond(space, at, side.inward());
        if (value.isPresent()) {
            return Bound.at(value.get(), true);
        }
        // A strict end the quantity takes no first value past. The run stops where the rule stops
        // and does not keep the place it stops at, which is what the two together say: read as no
        // end at all, such a run ran to the end of the order and held every value the bound
        // refuses; read as the value, it held the one value the bound refuses.
        return end.inclusive() ? null : Bound.at(at, false);
    }
}
