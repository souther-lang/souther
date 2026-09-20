package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.PlacesApart;
import souther.compiler.values.ValueSet;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.SequencedMap;
import java.util.Set;
import java.util.function.Function;

/**
 * One assignment of some positions that a region admits, or nothing.
 *
 * <p><b>A witness and not a representative.</b> What a region leaves a position is a run, and every
 * value of it is as good as any other until the next position is asked — at which point most of
 * them may leave nothing. Asked one position at a time and answered with the first value each run
 * offers, a set of conditions that has an assignment comes back as one that has none: the first
 * choice was not wrong about its own position and was wrong about the pair.
 *
 * <p>So what this is asked for is the assignment, and the values it tries are its own business. A
 * caller holding conditions it wants a row written under puts them to the region and is told whether
 * there is one, which is a question about the region rather than about the order values happen to
 * be offered in.
 *
 * <p><b>Not a proof of the opposite.</b> Coming back with nothing says these values were tried and
 * none of them was an assignment. A region that leaves a position a run without an end is sampled
 * rather than walked, so what is here is bounded and a longer search may find one — which is the
 * same thing {@link SearchRegion#emptiness()} promises of itself: not being empty is not a value
 * existing, and this is where a caller finds out which.
 *
 * <p>Apart from {@link LevelRealizer} on purpose. That one is asked where a row has to stand for it
 * to be at a coverage item, which is a question about a border; this is asked whether a set of
 * conditions has an assignment at all, which is a question about a region and has no item in it.
 * Answered together, the realizer would be deciding what a row is as well as where its item is.
 */
final class NumericWitness {

    /**
     * How many values of one position are tried before this gives up on it.
     *
     * <p>Small, and bounded for the reason every other walk here is: a run without an end is
     * sampled. What stepping past a value buys is the next position having something left, and a
     * condition relating two positions gives that up within a step or two of the end it is written
     * against — past which the values being tried are ones the same condition already refused.
     */
    private static final int VALUES_A_POSITION_IS_TRIED_AT =
            CompositionBudget.VALUES_A_POSITION_ON_THE_WAY_IS_TRIED_AT.maximum();

    /**
     * How many places of the run are walked past to find those values.
     *
     * <p>The other figure, because the two stopped being one number when the walk began stepping
     * over places the declarations and the rules refuse. This one bounds the looking: a run with no
     * end whose places are all refused is otherwise walked forever, and a reader told the figure
     * above where this one stopped the walk is sent to raise a number that changes nothing.
     */
    private static final int PLACES_A_POSITION_IS_LOOKED_AT =
            CompositionBudget.PLACES_A_POSITION_ON_THE_WAY_IS_LOOKED_AT.maximum();

    /**
     * Where each of {@code terms} may stand together inside {@code within}, or null where this found
     * no such assignment.
     *
     * @param on      what each position is counted on, or null for one this has no order for — which
     *                is a position no value is chosen at here, and the whole assignment is refused
     *                rather than made without it
     * @param looking what the declarations leave each position and what one crossing of such a set
     *                with a run may cost. Both, and from the one place that pairs them: a search
     *                given the sets alone would have to reach for an allowance, and what it reached
     *                for would be a budget nothing granted it
     */
    static Standing of(SearchRegion within, List<NumericTerm.FromOnePosition> terms,
                       Function<NumericTerm, Carrier> on, WitnessSearch looking) {
        // What the rules settle about the question, before any of it is looked for. Two ways for
        // them to settle it and both are the region as it was handed over: it may admit no
        // assignment at all, and it may admit one while leaving a position the question names
        // nowhere to stand. The second is not the first — an input holding an empty collection is a
        // value, and a position inside that collection has no value — and a walk that met either of
        // them would spend what it is allowed on values the rules refuse and come back naming a
        // figure.
        if (within.emptiness().isPresent() || leavesNothing(within, terms)) {
            return new Standing.ProvedImpossible();
        }
        SequencedMap<NumericTerm.FromOnePosition, Place> standing = new LinkedHashMap<>();
        java.util.Set<CompositionBudget> stoppedBy =
                java.util.EnumSet.noneOf(CompositionBudget.class);
        return walk(within, terms, 0, on, looking, standing, stoppedBy)
                ? Standing.Found.walked(standing)
                : new Standing.NotFound(stoppedBy);
    }

    /**
     * Whether the region leaves one of the positions the question names nowhere to stand.
     *
     * <p>Asked of the region as it was handed over and of nothing narrower. A position left nothing
     * once some other has been fixed is that fixing's answer and not the question's — another value
     * of the same position may leave it something — so a proof taken there would say of the whole
     * question what holds of one branch of it.
     */
    private static boolean leavesNothing(SearchRegion within,
                                         List<NumericTerm.FromOnePosition> terms) {
        return terms.stream().anyMatch(term ->
                within.projectionOf(term) instanceof NumericDomain.FormProjection.NothingIsLeft);
    }

    /**
     * Where the positions may stand together, or what this compiler knows about their standing
     * nowhere.
     *
     * <p>Three answers and not two. A walk that tried every value it had, a walk that stopped at a
     * figure of this compiler's, and rules that were shown to leave nothing all come back with no
     * assignment — and a reader may act on the third as they may act on neither of the others
     * (ADR-0091). Only the second names a figure somebody could raise.
     *
     * <p>Held as three cases rather than as a map beside a flag, so that a proof carrying a figure
     * or an assignment cannot be written down at all: those were the pairs a reader would have had
     * to know not to trust.
     */
    sealed interface Standing {

        /**
         * Where each position stands, which is an assignment the region admits.
         *
         * <p>In the order the walk fixed the positions in, which is the order a reader tells the
         * region of them in: the region is told one position at a time, and what it is told after
         * one is fixed is asked of a region that already knows it. So the order is part of what
         * this is, and two of these that place the same positions in two orders are two values:
         * held as a sequence, and not as a map, whose equality would not see it.
         *
         * <p>Made only by the walk that fixed the positions, which is what says what order they
         * were fixed in. A position is placed once.
         */
        final class Found implements Standing {

            private final List<Placed> inFixingOrder;

            private Found(List<Placed> inFixingOrder) {
                this.inFixingOrder = List.copyOf(inFixingOrder);
                Set<NumericTerm.FromOnePosition> seen = new HashSet<>();
                for (Placed each : this.inFixingOrder) {
                    if (!seen.add(each.position())) {
                        throw new IllegalArgumentException(
                                "a position is placed once: " + each.position());
                    }
                }
            }

            /** What the walk came to, its positions in the order it fixed them. */
            private static Found walked(SequencedMap<NumericTerm.FromOnePosition, Place> standing) {
                List<Placed> placed = new ArrayList<>();
                standing.forEach((position, place) -> placed.add(new Placed(position, place)));
                return new Found(placed);
            }

            /** One position and the place the walk put it at. */
            record Placed(NumericTerm.FromOnePosition position, Place place) {

                public Placed {
                    Objects.requireNonNull(position, "a place is a position's");
                    Objects.requireNonNull(place, "a position is placed somewhere");
                }
            }

            /** The positions and where each stands, in the order the walk fixed them. */
            List<Placed> inFixingOrder() {
                return inFixingOrder;
            }

            /** Where {@code position} stands, or null where this places no such position. */
            Place placeOf(NumericTerm.FromOnePosition position) {
                for (Placed each : inFixingOrder) {
                    if (each.position().equals(position)) {
                        return each.place();
                    }
                }
                return null;
            }

            @Override
            public boolean equals(Object other) {
                return other instanceof Found found && inFixingOrder.equals(found.inFixingOrder);
            }

            @Override
            public int hashCode() {
                return inFixingOrder.hashCode();
            }

            @Override
            public String toString() {
                return "Found" + inFixingOrder;
            }
        }

        /**
         * The rules leave the question nothing, which is the model's answer rather than this
         * compiler's.
         *
         * <p>No figure travels with it and no assignment: nothing was walked, because the proof was
         * there before any value was chosen.
         */
        record ProvedImpossible() implements Standing {}

        /**
         * Nothing was found, and nothing follows about whether an assignment exists.
         *
         * <p>{@code stoppedBy} is what a reader could raise, and it is empty as readily as not — a
         * walk that tried everything it had to try is not a walk that walked everything there is.
         */
        record NotFound(java.util.Set<CompositionBudget> stoppedBy) implements Standing {

            public NotFound {
                stoppedBy = java.util.Set.copyOf(stoppedBy);
            }
        }
    }

    /**
     * The walk from one position on, with the ones before it fixed in {@code within}.
     *
     * <p>Depth-first, and the region is narrowed as each is chosen rather than at the end: a value
     * that leaves the rest nothing is stepped past here, where there is still another to try, and
     * not reported once every position has been given one.
     */
    private static boolean walk(SearchRegion within, List<NumericTerm.FromOnePosition> terms,
                                int at,
                                Function<NumericTerm, Carrier> on,
                                WitnessSearch looking,
                                Map<NumericTerm.FromOnePosition, Place> standing,
                                java.util.Set<CompositionBudget> stoppedBy) {
        if (at == terms.size()) {
            return true;
        }
        NumericTerm.FromOnePosition term = terms.get(at);
        Carrier carrier = on.apply(term);
        if (carrier == null) {
            return false;
        }
        // Where the term runs under what has been fixed so far. The rules leaving it nothing here is
        // this branch's answer and not the question's: the values fixed above are what took it away,
        // and another of them may leave it something. So the branch ends and the caller steps on,
        // which is what it does with a value the rules refuse.
        //
        // The question's own answer was taken before any of this ran, where the region is the one
        // that was handed over — read back as a range there, it would be the widest answer there is
        // out of the narrowest region there is.
        NumericDomain.Bounds runs;
        switch (within.projectionOf(term)) {
            case NumericDomain.FormProjection.Within(NumericDomain.Bounds held) -> runs = held;
            case NumericDomain.FormProjection.NothingIsLeft _ -> {
                return false;
            }
            case null -> {
                return false;
            }
        }
        if (runs == null) {
            return false;
        }
        // The three narrowings this position stands under, read once and handed to the walk whole.
        // What the arithmetic leaves the number is one of them; the walk is held to the other two
        // at every place it reaches, and not only at the one it starts from.
        ValueSet admits = looking.toNarrowBy(term);
        PlacesApart apart = within.apartAt(term);
        Place first = carrier.somethingOtherThan(apart, runs, admits, looking.meter());
        if (first == null) {
            return false;
        }
        Outwards.Walked walked = Outwards.from(first, Count.of(1), carrier, runs,
                VALUES_A_POSITION_IS_TRIED_AT, PLACES_A_POSITION_IS_LOOKED_AT, admits, apart);
        for (Place tried : walked) {
            SearchRegion next = within.given(term, tried);
            if (next.emptiness().isPresent()) {
                continue;
            }
            standing.put(term, tried);
            if (walk(next, terms, at + 1, on, looking, standing, stoppedBy)) {
                return true;
            }
            standing.remove(term);
        }
        // What the walk of this position came to, read over the ways it can end rather than off one
        // of them. Each says something different about an empty hand, and a reading that asked only
        // whether a figure was met said the first of them about all three.
        switch (walked.ended()) {
            // Every value this position had to offer was tried and none of them led anywhere.
            case HAVING_TRIED_THEM_ALL -> { }
            // There were more, and a figure of this compiler's is why they were not tried, which is
            // what the caller is owed beside the empty hand. Which figure, because raising one of
            // them tries more of what the walk found and raising the other looks further for
            // something to find, and a reader handed the wrong one raises a number that reaches
            // nothing.
            case AT_THE_FIGURE_OF_CANDIDATES ->
                    stoppedBy.add(CompositionBudget.VALUES_A_POSITION_ON_THE_WAY_IS_TRIED_AT);
            case AT_THE_FIGURE_OF_PLACES_LOOKED_AT ->
                    stoppedBy.add(CompositionBudget.PLACES_A_POSITION_ON_THE_WAY_IS_LOOKED_AT);
            // And an order with no step to take, where the one place this named is not the whole of
            // what the position holds. Nothing is recorded, because what was left is a population
            // and what travels from here is figures: an entry made here would tell a reader to raise
            // a number that reaches none of it. Said as the arm it is rather than left to the figure
            // above being false, which is how the same fact was lost at the pair search.
            case WITH_NO_STEP_TO_TAKE -> { }
        }
        return false;
    }

    private NumericWitness() {}
}
