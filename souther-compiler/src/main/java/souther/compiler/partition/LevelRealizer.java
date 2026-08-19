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
            case Standing.OfAForm over -> ofAForm(over);
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
     * Every position of a form, at values that put the form where the item asks.
     *
     * <p>A bounded search over the whole numbers: each position runs between the ends its own rules
     * leave, the coefficients are the form's, and what is asked for is a level. Pruned by the two
     * things that settle it without looking — what the positions still to be chosen can add up to,
     * and whether the residue is a multiple of what their coefficients can make.
     *
     * <p><b>Three answers, and the difference between them is the point.</b> Exhausting a box every
     * position of which is bounded proves the level is out of reach; running past the budget, or
     * meeting a position nothing bounds, proves nothing at all (ADR-0091). Reported as one, a search
     * that ran out would take a coverage item away.
     *
     * <p>A side is asked for at the first level past the one it starts from, and then at the next,
     * for as many as {@link #LEVELS_OF_A_SIDE}. A point is asked for at its own level and nowhere
     * else: a level further out is a different point of the border, and offering it would answer a
     * question nobody asked.
     */
    private Realization ofAForm(Standing.OfAForm over) {
        LevelSpace levels = over.levels();
        List<Map.Entry<NumericTerm, java.math.BigDecimal>> terms =
                List.copyOf(over.form().coefs().entrySet());
        // A position whose values step takes whole numbers, and the level it is solved for has to be
        // one of them. Asked of the order the form's own values sit on, which is the one place that
        // says whether they step at all.
        boolean whole = levels.neighbour(new Level.ACount(Count.ZERO), Towards.ABOVE).isPresent();
        Towards outward = over.where() instanceof Criterion.Beyond beyond ? beyond.towards() : null;
        Level level = over.where().against();
        boolean bounded = true;
        for (int step = 0; step < (outward == null ? 1 : LEVELS_OF_A_SIDE); step++) {
            if (outward != null) {
                Optional<Level> past = levels.neighbour(level, outward);
                if (past.isEmpty()) {
                    return new Realization.Unknown(Realization.Unknown.Reason.NOTHING_COMPOSED_ONE);
                }
                level = past.get();
            }
            Search search = new Search(terms, whole);
            Map<NumericTerm, Place> found = search.solve(placeOf(level));
            if (found != null) {
                return new Realization.Found(found);
            }
            bounded &= search.exhaustive();
        }
        return bounded && outward == null ? new Realization.Impossible()
                : new Realization.Unknown(Realization.Unknown.Reason.THE_SEARCH_RAN_OUT);
    }

    /** How far out a side is looked at before the search gives up on it. A side is met anywhere past
     *  its own end, so the first level that a row can be written at stands for it; a box that holds
     *  none of the first few holds one only where the rules are shaped so that the whole search is
     *  worth its own answer. */
    private static final int LEVELS_OF_A_SIDE = 8;

    /** How many assignments the search will try before it stops and says it did not settle it. */
    private static final int STEPS_A_SEARCH_MAY_TAKE = 200_000;

    /**
     * The search itself: an assignment of every position of a form, or nothing.
     *
     * <p>Depth-first over the positions, each between the ends its rules leave. Two prunings, both
     * of them proofs rather than heuristics: what the remaining positions can sum to, and the
     * greatest common divisor of their coefficients, which the residue has to be a multiple of.
     */
    private final class Search {

        private final List<Map.Entry<NumericTerm, java.math.BigDecimal>> terms;
        private final boolean whole;
        private final Place[] at;
        private int taken;
        private boolean everyEndKnown = true;

        Search(List<Map.Entry<NumericTerm, java.math.BigDecimal>> terms, boolean whole) {
            this.terms = terms;
            this.whole = whole;
            this.at = new Place[terms.size()];
        }

        /** Whether what it walked was the whole of the box, which is what makes an empty answer a
         *  proof. */
        boolean exhaustive() {
            return everyEndKnown && taken < STEPS_A_SEARCH_MAY_TAKE;
        }

        Map<NumericTerm, Place> solve(Place target) {
            return walk(0, Count.number(target).at()) ? fixing() : null;
        }

        private Map<NumericTerm, Place> fixing() {
            Map<NumericTerm, Place> out = new LinkedHashMap<>();
            for (int i = 0; i < terms.size(); i++) {
                out.put(terms.get(i).getKey(), at[i]);
            }
            return out;
        }

        private boolean walk(int i, java.math.BigDecimal owed) {
            if (++taken > STEPS_A_SEARCH_MAY_TAKE) {
                return false;
            }
            java.math.BigDecimal coef = terms.get(i).getValue();
            NumericDomain.Bounds within = bounds(terms.get(i).getKey());
            java.math.BigDecimal low = endOf(within.min());
            java.math.BigDecimal high = endOf(within.max());
            if (i == terms.size() - 1) {
                // The last position is solved rather than tried: what is left over has to be its
                // coefficient's multiple, and the value that makes it up is one number.
                java.math.BigDecimal[] divided = owed.divideAndRemainder(coef);
                if (divided[1].signum() != 0 || (whole && divided[0].stripTrailingZeros().scale() > 0)
                        || below(divided[0], low) || above(divided[0], high)) {
                    return false;
                }
                at[i] = new Count(divided[0]);
                return true;
            }
            if (low == null || high == null) {
                // A position nothing bounds is not one this walks. Held at nothing, it is left where
                // the rules leave everything else and the answer says the search did not settle it.
                everyEndKnown = false;
                at[i] = Count.ZERO;
                return walk(i + 1, owed);
            }
            for (java.math.BigDecimal x = low; x.compareTo(high) <= 0;
                    x = x.add(java.math.BigDecimal.ONE)) {
                at[i] = new Count(x);
                if (walk(i + 1, owed.subtract(coef.multiply(x)))) {
                    return true;
                }
                if (taken > STEPS_A_SEARCH_MAY_TAKE) {
                    return false;
                }
            }
            return false;
        }

        private java.math.BigDecimal endOf(Endpoint end) {
            if (end == null || !(end.at() instanceof Count count)) {
                return null;
            }
            java.math.BigDecimal number = count.at();
            return whole ? number.setScale(0, end.inclusive()
                    ? java.math.RoundingMode.HALF_UP : java.math.RoundingMode.HALF_UP) : number;
        }

        private static boolean below(java.math.BigDecimal x, java.math.BigDecimal low) {
            return low != null && x.compareTo(low) < 0;
        }

        private static boolean above(java.math.BigDecimal x, java.math.BigDecimal high) {
            return high != null && x.compareTo(high) > 0;
        }
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
