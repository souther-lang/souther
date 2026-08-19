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
        Place common = commonPlace(bounds(two.on()), bounds(two.against()), two.of(),
                two.where().against().asACount());
        if (common == null) {
            return new Realization.Unknown(Realization.Unknown.Reason.NOTHING_COMPOSED_ONE);
        }
        // Where the first has to stand relative to the second: the place the level's distance from
        // it, and then whatever the item asks of that place. Arithmetic on the carrier's counts and
        // not a walk along it — a walk is an addition that only exists where the order has a
        // smallest step, so a rule over two decimals had no pair anything could compose.
        Place from = movedBy(common, two.where().against(), two.of());
        if (from == null) {
            return new Realization.Unknown(Realization.Unknown.Reason.NOTHING_COMPOSED_ONE);
        }
        Place at = placeMeeting(relativeTo(two.where(), from, two.of()), two.of(), bounds(two.on()));
        if (at == null || !meets(two.where(), at.compareTo(from))) {
            return new Realization.Unknown(Realization.Unknown.Reason.NOTHING_COMPOSED_ONE);
        }
        Map<NumericTerm, Place> fixing = new LinkedHashMap<>();
        fixing.put(two.on(), at);
        fixing.put(two.against(), common);
        return new Realization.Found(fixing);
    }

    /**
     * The place {@code from} moved by the distance a level names, or null where the carrier holds
     * none there.
     *
     * <p>The distance is a number on the carrier's counts, so this is addition. Where the carrier's
     * values do not count there is no distance to add, and the only level such a quantity takes is
     * the one where the two meet — so the place is the one they meet at and any other level names
     * nothing.
     */
    private static Place movedBy(Place from, Level level, Carrier carrier) {
        Count apart = level.asACount();
        if (!carrier.counts()) {
            return apart.signum() == 0 ? from : null;
        }
        return carrier.onTheGrid(Count.number(from).plus(apart));
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
        // In the form's own order and not the map's. A form is a map, so the order its coefficients
        // were recorded in is a hash order — and which position is solved last decides whether the
        // walk finds an answer inside its budget, so an answer that depended on it would depend on
        // nothing a reader can see.
        List<Map.Entry<NumericTerm, java.math.BigDecimal>> terms =
                AffineReading.ordered(over.form());
        // A position whose values step takes whole numbers, and the level it is solved for has to be
        // one of them. Asked of the order the form's own values sit on, which is the one place that
        // says whether they step at all.
        boolean whole = levels.neighbour(new Level.ACount(Count.ZERO), Towards.ABOVE).isPresent();
        boolean bounded = true;
        for (Level level : levelsToTry(levels, over.where())) {
            Search search = new Search(terms, over.of(), whole);
            Map<NumericTerm, Place> found = search.solve(level.asACount());
            if (found != null) {
                return new Realization.Found(found);
            }
            bounded &= search.exhaustive();
        }
        // A point asks for one level and a side asks for any level past one, so only the first can
        // be settled by looking: a walk of the whole box that reaches the level nothing else does is
        // a proof, and a side that none of the levels tried reached is a side this stopped looking
        // at.
        return bounded && over.where() instanceof Criterion.AtTheLevel
                ? new Realization.Impossible()
                : new Realization.Unknown(Realization.Unknown.Reason.THE_SEARCH_RAN_OUT);
    }

    /**
     * The levels a row at this item could stand at, nearest first.
     *
     * <p>A point stands at one level and nowhere else. A side is met anywhere past its own end, and
     * a class of everything but one level is met at either of the two beside it — so both are asked
     * for at the levels nearest the one they are written against, outward, until the budget runs
     * out. Which is why a side that came back empty settles nothing while a point may.
     */
    private static List<Level> levelsToTry(LevelSpace levels, Criterion where) {
        Level from = where.against();
        return switch (where) {
            case Criterion.AtTheLevel _ -> List.of(from);
            case Criterion.Beyond beyond -> outward(levels, from, beyond.towards());
            case Criterion.AnythingBut _ -> {
                List<Level> either = new java.util.ArrayList<>(outward(levels, from, Towards.ABOVE));
                either.addAll(outward(levels, from, Towards.BELOW));
                yield either;
            }
        };
    }

    private static List<Level> outward(LevelSpace levels, Level from, Towards towards) {
        List<Level> out = new java.util.ArrayList<>();
        Level at = from;
        for (int step = 0; step < LEVELS_OF_A_SIDE; step++) {
            // Some level past this one, which an order whose values fill answers as readily as one
            // that steps. Asked for the neighbour, a side of a border over decimals had no level to
            // look at and came back saying the search had stopped without one having run.
            Optional<Level> past = levels.somethingBeyond(at, towards);
            if (past.isEmpty()) {
                break;
            }
            at = past.get();
            out.add(at);
        }
        return out;
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
        private final Carrier carrier;
        private final boolean whole;
        private final Place[] at;
        private int taken;
        private boolean everyEndKnown = true;

        Search(List<Map.Entry<NumericTerm, java.math.BigDecimal>> terms, Carrier carrier,
               boolean whole) {
            this.terms = terms;
            this.carrier = carrier;
            this.whole = whole;
            this.at = new Place[terms.size()];
        }

        /** Whether what it walked was the whole of the box, which is what makes an empty answer a
         *  proof. */
        boolean exhaustive() {
            return everyEndKnown && taken < STEPS_A_SEARCH_MAY_TAKE;
        }

        Map<NumericTerm, Place> solve(Count target) {
            return walk(0, target.at()) ? fixing() : null;
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
            // What the positions from here on can add up to, and what their coefficients can make.
            // Both are proofs: a residue outside the reach of everything still to be chosen is one
            // no assignment of them arrives at, and a residue that is not a multiple of what their
            // coefficients can make is one none of them lands on. Without them a wide box is walked
            // one step at a time until the budget runs out, and a level the rules truly leave
            // nothing at comes back as a search that stopped rather than as the proof it is.
            if (outOfReach(i, owed) || offTheLattice(i, owed)) {
                return false;
            }
            java.math.BigDecimal coef = terms.get(i).getValue();
            NumericDomain.Bounds within = bounds(terms.get(i).getKey());
            // Narrowed by what the positions after this one can add up to. Used to reject a choice
            // after making it, a box a million wide is walked a million times and the budget runs
            // out on `a + b <= 2000000` — an equation with one answer. Used to bound the walk, that
            // answer is the only value tried.
            NumericDomain.Bounds left = leaving(i + 1, owed, coef, within);
            if (i == terms.size() - 1) {
                // The last position is solved rather than tried. Where its values step, what is left
                // over has to be its coefficient's multiple; where they fill, it is a division and
                // the answer is whatever number it comes to — asked for a whole number there, a form
                // over decimals came back unsolvable at every level it holds.
                java.math.BigDecimal solved;
                if (whole) {
                    java.math.BigDecimal[] divided = owed.divideAndRemainder(coef);
                    if (divided[1].signum() != 0) {
                        return false;
                    }
                    solved = divided[0];
                } else {
                    try {
                        solved = owed.divide(coef);
                    } catch (ArithmeticException nonTerminating) {
                        // A quotient with no end is not a value a model writes, and rounding one
                        // would offer a row that misses the level by however much was rounded off.
                        everyEndKnown = false;
                        return false;
                    }
                }
                // Held against the ends themselves, which say whether they are their own values. A
                // bound of `> 0` leaves one and not zero, and rounding the end to a number first
                // loses which of the two it is.
                if (!left.admits(new Count(solved))) {
                    return false;
                }
                at[i] = new Count(solved);
                return true;
            }
            java.math.BigDecimal low = endOf(left.min(), true);
            java.math.BigDecimal high = endOf(left.max(), false);
            if (low == null || high == null || !whole) {
                // Not a position this can walk. One nothing bounds has no ends to run between; one
                // whose values fill has no next value to step to, so there is no enumeration of it
                // at all. Either way this takes one value the rules admit and goes on, and says that
                // what it walked was not the whole of the box — a proof may only come out of a walk
                // that was.
                //
                // Which value is the carrier's answer and not this one's. Worked out from the
                // numbers, an end the rules exclude was taken as one they leave and an end above was
                // not consulted at all, so the row offered was one the position refuses and the
                // report said every candidate had been rejected.
                everyEndKnown = false;
                // Which value it takes is chosen against what the rest can reach, not off the end of
                // its own range: the residue has to be something the positions after it arrive at,
                // and a value picked without asking leaves a form over three or more filled
                // positions unsolved wherever the first guess happens not to work out.
                Place inside = carrier.somethingInside(left.min(), left.max());
                if (inside == null || !(inside instanceof Count taken)) {
                    return false;
                }
                at[i] = taken;
                return walk(i + 1, owed.subtract(coef.multiply(taken.at())));
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

        /**
         * One end of what the rules leave a position, as a whole number this can start or stop at.
         *
         * <p>Asked only to bound an enumeration, which only a position whose values step has. Where
         * they fill, what a value inside the ends is is the carrier's answer and whether a solved one
         * is inside them is the ends' own.
         *
         * <p>Rounded inwards and never outwards, and the excluded end excluded. A bound of
         * {@code > 0} leaves one, not zero; a bound of {@code >= 2.4} over whole numbers leaves
         * three, not two. Rounded the other way, the search offers a value the position refuses and
         * the decoder turns the row down — which arrives as every candidate having been rejected,
         * and reads as the model refusing an edge it admits.
         */
        /**
         * What the rules leave this position, narrowed to the values that leave the rest a residue
         * they can reach.
         *
         * <p>What the positions after this one can add up to is an interval; what this one has to
         * contribute for the residue to land in it is another. Both are proofs — a value outside
         * either is one no assignment of the rest completes — so the walk runs between them rather
         * than between the position's own ends.
         */
        private NumericDomain.Bounds leaving(int rest, java.math.BigDecimal owed,
                                             java.math.BigDecimal coef,
                                             NumericDomain.Bounds within) {
            java.math.BigDecimal[] reach = reach(rest);
            if (reach == null || coef.signum() == 0) {
                return within;
            }
            // owed - coef * x must lie in [reach0, reach1], so coef * x lies in
            // [owed - reach1, owed - reach0].
            java.math.BigDecimal one = owed.subtract(reach[1])
                    .divide(coef, java.math.MathContext.DECIMAL64);
            java.math.BigDecimal other = owed.subtract(reach[0])
                    .divide(coef, java.math.MathContext.DECIMAL64);
            return new NumericDomain.Bounds(
                    Endpoint.lower(within.min(), Endpoint.inclusive(new Count(one.min(other)))),
                    Endpoint.upper(within.max(), Endpoint.inclusive(new Count(one.max(other)))));
        }

        /**
         * The least and the greatest the positions from {@code i} on can add up to, or null where
         * one of them is unbounded and there is nothing to say.
         */
        private java.math.BigDecimal[] reach(int i) {
            java.math.BigDecimal least = java.math.BigDecimal.ZERO;
            java.math.BigDecimal most = java.math.BigDecimal.ZERO;
            for (int j = i; j < terms.size(); j++) {
                NumericDomain.Bounds within = bounds(terms.get(j).getKey());
                java.math.BigDecimal coef = terms.get(j).getValue();
                java.math.BigDecimal low = numberOf(within.min());
                java.math.BigDecimal high = numberOf(within.max());
                if (low == null || high == null) {
                    return null;
                }
                java.math.BigDecimal one = coef.multiply(low);
                java.math.BigDecimal other = coef.multiply(high);
                least = least.add(one.min(other));
                most = most.add(one.max(other));
            }
            return new java.math.BigDecimal[] {least, most};
        }

        /** Whether the residue is outside everything the positions from {@code i} on can add up to,
         *  which no assignment of them arrives at. */
        private boolean outOfReach(int i, java.math.BigDecimal owed) {
            java.math.BigDecimal[] rest = reach(i);
            return rest != null && (owed.compareTo(rest[0]) < 0 || owed.compareTo(rest[1]) > 0);
        }

        /**
         * Whether the residue is off the lattice the positions from {@code i} on can land on.
         *
         * <p>Only where their values step: over whole numbers what {@code Σ c·x} takes is exactly
         * the multiples of the coefficients' greatest common divisor (Bézout), so a residue that is
         * not one is a residue none of them reaches. Where the values fill there is no lattice and
         * this says nothing.
         */
        private boolean offTheLattice(int i, java.math.BigDecimal owed) {
            if (!whole) {
                return false;
            }
            java.math.BigDecimal step = LevelSpace.stepOf(
                    terms.subList(i, terms.size()).stream().map(Map.Entry::getValue).toList());
            return step.signum() != 0 && owed.remainder(step).signum() != 0;
        }

        private static java.math.BigDecimal numberOf(Endpoint end) {
            return end == null || !(end.at() instanceof Count count) ? null : count.at();
        }

        private java.math.BigDecimal endOf(Endpoint end, boolean low) {
            if (end == null || !(end.at() instanceof Count count)) {
                return null;
            }
            java.math.BigDecimal number = count.at();
            java.math.BigDecimal onTheGrid = number.setScale(0,
                    low ? java.math.RoundingMode.CEILING : java.math.RoundingMode.FLOOR);
            // An end the rules exclude, already on the grid, is one value further in.
            boolean atTheEnd = onTheGrid.compareTo(number) == 0;
            return end.inclusive() || !atTheEnd ? onTheGrid
                    : onTheGrid.add(java.math.BigDecimal.valueOf(low ? 1 : -1));
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
                                    Carrier carrier, Count apart) {
        NumericDomain.Bounds moved = carrier.counts() ? shifted(on, apart.negate()) : on;
        Endpoint min = Endpoint.lower(moved == null ? null : moved.min(),
                against == null ? null : against.min());
        Endpoint max = Endpoint.upper(moved == null ? null : moved.max(),
                against == null ? null : against.max());
        return carrier.somethingInside(min, max);
    }

    /**
     * What the rules leave one position, read as what they leave the other one standing that far
     * from it.
     *
     * <p>The distance is part of the question. Two positions each left {@code [0, 100]} have every
     * place in common where the rule cuts where they meet, and only {@code [1, 100]} where it holds
     * them one apart — the pair at zero would put the first at minus one, which its own rules
     * refuse. Intersected without the distance, the search offered exactly that pair and the report
     * said every value tried had been refused.
     */
    private static NumericDomain.Bounds shifted(NumericDomain.Bounds bounds, Count by) {
        if (bounds == null) {
            return null;
        }
        return new NumericDomain.Bounds(moved(bounds.min(), by), moved(bounds.max(), by));
    }

    private static Endpoint moved(Endpoint end, Count by) {
        return end == null || !(end.at() instanceof Count count) ? end
                : new Endpoint(count.plus(by), end.inclusive());
    }

    private NumericDomain.Bounds bounds(NumericTerm term) {
        NumericDomain.Bounds held = within == null ? null : within.apply(term);
        return held == null ? new NumericDomain.Bounds(null, null) : held;
    }

    private static Place placeOf(Level level) {
        return switch (level) {
            case Level.OnACarrier on -> on.at();
            case Level.ACount count -> count.at();
        };
    }
}
