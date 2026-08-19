package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.BoundaryDomain;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.function.Function;

/**
 * Where each position has to stand for a row to be at one coverage item.
 *
 * <p><b>Apart from {@link BorderQuantity} on purpose.</b> What a border means and where a row at one
 * of its points is are two questions: the first is settled by the rule and the order it cut, and the
 * second depends on what every other rule leaves, on what this compiler can search, and on how long
 * it is willing to look. Answered together, a quantity would carry a solver and every reading of a
 * border would be paying for one.
 *
 * <p>What it is handed is a {@link Standing} — a constraint, not a shape of line — so a quantity
 * added later brings work here only where it needs a kind of search that is not already written.
 *
 * <p>Nothing here decides that an item cannot be reached. A refusal is a refusal of what was tried,
 * and {@link Realization} keeps that apart from a proof: read as one, a search that ran out said the
 * model refuses an edge it merely could not compose (ADR-0091).
 */
public final class LevelRealizer {

    private final Function<NumericTerm, NumericDomain.Bounds> within;

    /**
     * @param within what the rules leave each position, on its own carrier. A term nothing was
     *               recorded about is one the rules leave everything
     */
    public LevelRealizer(Function<NumericTerm, NumericDomain.Bounds> within) {
        this.within = within;
    }

    /** Where the positions have to stand, or why this found nowhere. */
    public Realization realize(Standing standing) {
        return switch (standing) {
            case Standing.OfOneCoordinate one -> ofOne(one);
            case Standing.OfTwoOnOneCarrier two -> ofTwo(two);
        };
    }

    /** One position at a place of its own carrier that the item accepts. */
    private Realization ofOne(Standing.OfOneCoordinate one) {
        Place at = placeMeeting(one.where(), one.of(), bounds(one.term()));
        return at == null ? new Realization.Unknown(Realization.Unknown.Reason.NOTHING_COMPOSED_ONE)
                : new Realization.Found(Map.of(one.term(), at));
    }

    /**
     * Two positions, both fixed at once.
     *
     * <p>Which is the whole of what makes the row one at the item. A search that settled one and left
     * the other to its own range would produce a row beside the line as readily as one on it.
     *
     * <p>The place the second stands at is a place both of them admit, which is the rules' answer
     * about the pair. Where they leave none, nothing is composed — and that is reported as a search
     * that found nothing rather than as a proof, because two ranges leaving no place in common is a
     * fact about the ranges and the pair may be refused or admitted by a rule neither range holds.
     */
    private Realization ofTwo(Standing.OfTwoOnOneCarrier two) {
        Place common = commonPlace(bounds(two.on()), bounds(two.against()), two.of());
        if (common == null) {
            return new Realization.Unknown(Realization.Unknown.Reason.NOTHING_COMPOSED_ONE);
        }
        // Where the first has to stand relative to the second: the place so many of the carrier's
        // steps from it, and then whatever the item asks of that place.
        Optional<Place> from = stepped(common, stepsOf(two.where().against()), two.of());
        if (from.isEmpty()) {
            return new Realization.Unknown(Realization.Unknown.Reason.NOTHING_COMPOSED_ONE);
        }
        Place at = placeMeeting(relativeTo(two.where(), from.get(), two.of()), two.of(),
                bounds(two.on()));
        if (at == null || !meets(two.where(), at.compareTo(from.get()))) {
            return new Realization.Unknown(Realization.Unknown.Reason.NOTHING_COMPOSED_ONE);
        }
        Map<NumericTerm, Place> fixing = new LinkedHashMap<>();
        fixing.put(two.on(), at);
        fixing.put(two.against(), common);
        return new Realization.Found(fixing);
    }

    /**
     * The item read as a question about one place of one carrier, given where the other position
     * stands.
     *
     * <p>A level of a distance says nothing about a carrier's order until the other end of it is
     * known. Once it is, an item about the pair is an item about one place — which is why the two
     * are searched for by one procedure rather than by two that agreed by being written alike.
     */
    private static Criterion relativeTo(Criterion where, Place from, Carrier of) {
        Level here = new Level.OnACarrier(of, from);
        return switch (where) {
            case Criterion.AtTheLevel _ -> new Criterion.AtTheLevel(here);
            case Criterion.Beyond beyond -> new Criterion.Beyond(here, beyond.towards());
            case Criterion.AnythingBut _ -> new Criterion.AnythingBut(here);
        };
    }

    /** Whether a place standing {@code order} from where the item is against meets it. */
    private static boolean meets(Criterion where, int order) {
        return switch (where) {
            case Criterion.AtTheLevel _ -> order == 0;
            case Criterion.Beyond beyond -> beyond.towards() == Towards.ABOVE ? order > 0 : order < 0;
            case Criterion.AnythingBut _ -> order != 0;
        };
    }

    /**
     * A place of {@code carrier} the item accepts, or null where this composes none.
     *
     * <p>Composed and then asked. Which place stands at an item and whether a place is at that item
     * are two answers, and the second already exists — worked out apart, the two came apart. So what
     * is composed is put back to the item, and a place the item does not accept stands for nothing:
     * a row offered for a side that is really at the point against the line is a row an author pastes
     * and re-measures to find the item still uncovered.
     */
    private static Place placeMeeting(Criterion where, Carrier carrier,
                                      NumericDomain.Bounds bounds) {
        Place offered = switch (where) {
            case Criterion.AtTheLevel at -> placeOf(at.at());
            case Criterion.Beyond beyond -> {
                Endpoint past = Endpoint.exclusive(placeOf(beyond.from()));
                Endpoint low = beyond.towards() == Towards.ABOVE
                        ? Endpoint.lower(past, bounds.min()) : bounds.min();
                Endpoint high = beyond.towards() == Towards.BELOW
                        ? Endpoint.upper(past, bounds.max()) : bounds.max();
                yield carrier.somethingInside(low, high);
            }
            case Criterion.AnythingBut other ->
                    carrier.somethingOtherThan(List.of(placeOf(other.excluded())), bounds);
        };
        if (offered == null) {
            return null;
        }
        // The grid is asked first and separately. What a carrier's values are spaced by says what a
        // place may be sharpened onto and does not promise that every number between two counts is
        // one of them, which is the carrier's question rather than the item's.
        Place onTheGrid = carrier.onTheGrid(offered);
        return onTheGrid != null && accepts(where, onTheGrid) ? onTheGrid : null;
    }

    private static boolean accepts(Criterion where, Place at) {
        return meets(where, at.compareTo(placeOf(where.against())));
    }

    /**
     * A place both positions of a line between them can hold, or null where their rules leave none.
     *
     * <p>What proves a row can be written on such a line. The line is where the two positions are
     * equal, so a row on it writes one place at both — and whether one exists is the two positions'
     * ranges read together, which is a question the rules answer without anything being built.
     *
     * <p>Null is not a proof of the opposite. Two ranges that leave no place leave none, and that is a
     * fact about the rules; a range this could not read in full is a range this did not read, and the
     * caller is the one holding whether that happened.
     */
    public static Place commonPlace(NumericDomain.Bounds on, NumericDomain.Bounds against,
                                    Carrier carrier) {
        Endpoint min = Endpoint.lower(on == null ? null : on.min(),
                against == null ? null : against.min());
        Endpoint max = Endpoint.upper(on == null ? null : on.max(),
                against == null ? null : against.max());
        return carrier.somethingInside(min, max);
    }

    /** The place {@code steps} of the carrier's own steps from {@code from}, or nothing where the
     *  carrier names no value that far. */
    private static Optional<Place> stepped(Place from, long steps, Carrier carrier) {
        BoundaryDomain domain = BoundaryDomain.on(carrier);
        Optional<Place> walked = Optional.of(from);
        for (long taken = 0; taken < Math.abs(steps); taken++) {
            walked = walked.flatMap(at -> steps > 0 ? domain.successor(at) : domain.predecessor(at));
        }
        return walked;
    }

    private NumericDomain.Bounds bounds(NumericTerm term) {
        NumericDomain.Bounds held = within == null ? null : within.apply(term);
        return held == null ? new NumericDomain.Bounds(null, null) : held;
    }

    private static long stepsOf(Level level) {
        return level instanceof Level.ACount count ? count.at().at().longValueExact() : 0;
    }

    private static Place placeOf(Level level) {
        return switch (level) {
            case Level.OnACarrier on -> on.at();
            case Level.ACount count -> count.at();
        };
    }

    /** A count as a level, for a caller holding one. */
    public static Level at(Count count) {
        return new Level.ACount(count);
    }
}
