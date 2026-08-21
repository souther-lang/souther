package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.BoundaryDomain;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Towards;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

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

    private final souther.compiler.inputs.Quantities rules;

    /**
     * @param rules what the declarations reaching this behavior's input leave its quantities, which
     *              is what a row has to be written inside. Taken whole rather than as an end per
     *              position: a rule relating two positions is not in either of their ranges, so a
     *              search handed the ranges walks a box with a corner cut off it that it cannot see
     *              — and offers a row in the corner
     */
    public LevelRealizer(souther.compiler.inputs.Quantities rules) {
        if (rules == null) {
            throw new IllegalArgumentException(
                    "a search looks inside what the rules leave, and there is always a reading of"
                            + " them: an input nothing was written about is one they leave"
                            + " everything, which is an answer and not an absence");
        }
        this.rules = rules;
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
                two.where().anchor().asACount());
        if (common == null) {
            return new Realization.Unknown(Realization.Unknown.Reason.NOTHING_COMPOSED_ONE);
        }
        // Where the first has to stand relative to the second: the place the level's distance from
        // it, and then whatever the item asks of that place. Arithmetic on the carrier's counts and
        // not a walk along it — a walk is an addition that only exists where the order has a
        // smallest step, so a rule over two decimals had no pair anything could compose.
        // Null where the carrier's arithmetic could not put the item's levels beside the place the
        // other position stands at. Reported as a search that composed nothing, which is what it is
        // — read on, an item with no level in it was handed to a reader that asks where its level
        // falls.
        Criterion here = relativeTo(two.where(), common, two.of());
        Place at = here == null ? null : placeMeeting(here, two.of(), bounds(two.on()));
        if (at == null) {
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
     * for as many as {@link LevelCandidateSource} offers. Which levels those are, and how many, is
     * that one's answer: whether a row can be composed at one of them is this one's, and the two are
     * apart so that how long this is willing to look does not read as a fact about the order.
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
        for (Level level : LevelCandidateSource.forItem(over.where(), levels)) {
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

    /** How many assignments the search will try before it stops and says it did not settle it. */
    private static final int STEPS_A_SEARCH_MAY_TAKE = 200_000;

    /** How often one search reads the declarations again with a position fixed. Each of them is a
     *  reading of every rule reaching the form's positions, and what it buys is skipping
     *  assignments the rules refuse — worth paying for a search that ends quickly and not for one
     *  walking a box a hundred thousand wide. */
    private static final int HOW_OFTEN_THE_RULES_ARE_ASKED_AGAIN = 2_000;


    /** How far a derived end is written out where the division that makes it does not end. Any
     *  number of them is sound while the rounding goes outward; this many keeps the bound close
     *  enough that the walk it bounds is still short. */
    private static final int DIGITS_A_DERIVED_END_KEEPS = 32;

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
        private int asked;
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
            return walk(0, target.at(), rules) ? fixing() : null;
        }

        private Map<NumericTerm, Place> fixing() {
            Map<NumericTerm, Place> out = new LinkedHashMap<>();
            for (int i = 0; i < terms.size(); i++) {
                out.put(terms.get(i).getKey(), at[i]);
            }
            return out;
        }

        private boolean walk(int i, java.math.BigDecimal owed, souther.compiler.inputs.Quantities here) {
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
            NumericDomain.Bounds within = bounds(here, terms.get(i).getKey());
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
                // And the rules with every position of the form fixed, which is the one place a
                // whole assignment exists to be held against them. A value inside each position's
                // own ends can still be one no value of the record has beside the others, and this
                // is the step that is not given up: what is handed back is an assignment the rules
                // were not shown to refuse.
                if (!theRulesHaveNotRefused()) {
                    at[i] = null;
                    return false;
                }
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
                souther.compiler.inputs.Quantities next = narrowing(here, terms.get(i).getKey(), taken.at());
                if (next == null) {
                    return false;
                }
                at[i] = taken;
                return walk(i + 1, owed.subtract(coef.multiply(taken.at())), next);
            }
            for (java.math.BigDecimal x = low; x.compareTo(high) <= 0;
                    x = x.add(java.math.BigDecimal.ONE)) {
                // What the rules leave once this position holds this value. A value they leave
                // nothing beside is skipped here rather than offered and refused where the row is
                // built: refused there, one candidate coming back rejected is reported as every
                // value having been tried.
                souther.compiler.inputs.Quantities next = narrowing(here, terms.get(i).getKey(), x);
                if (next == null) {
                    continue;
                }
                at[i] = new Count(x);
                if (walk(i + 1, owed.subtract(coef.multiply(x)), next)) {
                    return true;
                }
                if (taken > STEPS_A_SEARCH_MAY_TAKE) {
                    return false;
                }
            }
            return false;
        }

        /**
         * The rules with one more position fixed, or null where they are then left nothing.
         *
         * <p>Narrowing, and only that. Null is a proof and the value is skipped on it, so a walk
         * that skips every one of them has still walked everything there was.
         *
         * <p><b>Asked while it is worth asking.</b> Each of these reads the declarations reaching the
         * positions again, and a box wide enough to walk for a hundred thousand steps is wide enough
         * to read them a hundred thousand times. Past {@link #HOW_OFTEN_THE_RULES_ARE_ASKED_AGAIN}
         * the walk carries on against what the rules left before anything was fixed, which is wider
         * and is sound: it offers assignments this would have skipped, and skips none it would have
         * kept.
         *
         * <p>What giving this up may not give up is the answer. An assignment out of the wider box
         * that nothing held against the rules is one the record can refuse, and offered as a row it
         * comes back refused where it is built — which is the defect this reading exists to remove,
         * arriving by way of a budget. So the last step is {@link #theRulesHaveNotRefused} and is
         * not budgeted.
         */
        private souther.compiler.inputs.Quantities narrowing(souther.compiler.inputs.Quantities here, NumericTerm term,
                                    java.math.BigDecimal at) {
            if (asked >= HOW_OFTEN_THE_RULES_ARE_ASKED_AGAIN) {
                return here;
            }
            asked++;
            souther.compiler.inputs.Quantities next = here.given(term, new Count(at));
            return next.emptiness().isPresent() ? null : next;
        }

        /**
         * Whether the rules, with every position of the form fixed at what the walk chose, were not
         * shown to leave nothing.
         *
         * <p>Not that a value exists. Nothing here builds one, and the rules leaving something is
         * not the same as something being writable — what settles that is the row itself, where it
         * is built. What this refuses is narrower and is the whole of what was wrong: an assignment
         * the rules are already known to refuse, offered as a row and reported as though the point
         * had nothing at it.
         *
         * <p>Asked of the whole assignment and not of the last position, because that is what an
         * assignment is. Where the narrowing above ran out, the values chosen before this one were
         * never put to the rules at all, so asking about the last of them alone would hold the walk
         * to nothing it had not already checked.
         */
        private boolean theRulesHaveNotRefused() {
            java.util.Map<NumericTerm, Count> all = new LinkedHashMap<>();
            for (int j = 0; j < terms.size(); j++) {
                if (at[j] instanceof Count count) {
                    all.put(terms.get(j).getKey(), count);
                }
            }
            return rules.given(all).emptiness().isEmpty();
        }

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
            java.math.BigDecimal one = owed.subtract(reach[1]);
            java.math.BigDecimal other = owed.subtract(reach[0]);
            java.math.BigDecimal low = quotient(one, coef, java.math.RoundingMode.FLOOR)
                    .min(quotient(other, coef, java.math.RoundingMode.FLOOR));
            java.math.BigDecimal high = quotient(one, coef, java.math.RoundingMode.CEILING)
                    .max(quotient(other, coef, java.math.RoundingMode.CEILING));
            return new NumericDomain.Bounds(
                    Endpoint.lower(within.min(), Endpoint.inclusive(new Count(low))),
                    Endpoint.upper(within.max(), Endpoint.inclusive(new Count(high))));
        }

        /**
         * A quotient that is exact where the division ends, and rounded the way {@code towards} says
         * where it does not.
         *
         * <p><b>Outward and never inward.</b> What this bounds is a proof — a value outside it is one
         * no assignment of the rest completes — so a bound rounded the wrong way takes a value the
         * box holds out of the walk, and a walk that then finds nothing calls the level unreachable.
         * Rounded to sixteen digits at the nearest, {@code a = 10000000000000001} was rounded to
         * {@code 10000000000000000} and the one pair that meets the line was proved not to exist.
         */
        private static java.math.BigDecimal quotient(java.math.BigDecimal owed,
                                                     java.math.BigDecimal coef,
                                                     java.math.RoundingMode towards) {
            try {
                return owed.divide(coef);
            } catch (ArithmeticException noEnd) {
                return owed.divide(coef, DIGITS_A_DERIVED_END_KEEPS, towards);
            }
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
    private static Criterion relativeTo(Criterion where, Place common, Carrier of) {
        // Every level of the item read as the place it lands on once the other end of the line is
        // known. Mapped one level at a time and not by handing one place to all of them: a run has
        // two ends and a line between them, and a mapping that gave them all the same place left a
        // run that said nothing about which side of the line it lay — so a search took whatever the
        // declared domain offered first and a row on the line came back for a point past it.
        // Null where the carrier's arithmetic puts a level nowhere. Which end that happens at
        // decides what it means: a line with no place is an item this order cannot be read as at
        // all, and a run's far end with no place is a run that reaches as far as the carrier does.
        java.util.function.UnaryOperator<Level> onto = level -> {
            Place at = movedBy(common, level, of);
            return at == null ? null : new Level.OnACarrier(of, at);
        };
        return switch (where) {
            case Criterion.AtTheLevel at -> only(new Criterion.AtTheLevel(onto.apply(at.at())),
                    onto.apply(at.at()));
            case Criterion.Within within -> {
                Band run = within.band().mappedBy(onto);
                yield run == null ? null : new Criterion.Within(run,
                        within.except() == null ? null : onto.apply(within.except()),
                        within.away());
            }
            case Criterion.AnythingBut other ->
                    only(new Criterion.AnythingBut(onto.apply(other.excluded())),
                            onto.apply(other.excluded()));
        };
    }

    /** An item, unless the level it is written against has no place on this order. */
    private static Criterion only(Criterion made, Level against) {
        return against == null ? null : made;
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
            // From the end the line is at, which is what makes the row one beside the boundary
            // rather than one at the far side of the partition. The point carries which end that is
            // and is not asked for it again: handed it a second time, a caller could ask for a run
            // to be read from the end it is not named for, which is the shape of one decision given
            // from two places.
            case Criterion.Within within ->
                    within.somewhereInside(carrier, bounds.min(), bounds.max());
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
        return onTheGrid != null && accepts(where, carrier, onTheGrid) ? onTheGrid : null;
    }

    /**
     * Whether a place of {@code carrier} is at this item.
     *
     * <p>The item's own answer and not a second reading of it. Whether a value stands at an item is
     * one question with one answer ({@link Criterion#holds}); worked out again from an order and a
     * level the item was written against, the two came apart wherever the item is a run — a run has
     * two ends and a line, and one comparison cannot say all three.
     */
    private static boolean accepts(Criterion where, Carrier carrier, Place at) {
        return where.holds(new Level.OnACarrier(carrier, at));
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
        return bounds(rules, term);
    }

    /** The same, of the rules as some of the positions have been fixed. */
    private static NumericDomain.Bounds bounds(souther.compiler.inputs.Quantities rules,
                                               NumericTerm term) {
        NumericDomain.Bounds held = rules.runsBetween(term);
        return held == null ? new NumericDomain.Bounds(null, null) : held;
    }

    private static Place placeOf(Level level) {
        return switch (level) {
            case Level.OnACarrier on -> on.at();
            case Level.ACount count -> count.at();
        };
    }
}
