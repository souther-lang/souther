package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.check.ClassMembers;
import souther.compiler.check.HeldClass;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.PlacesApart;
import souther.compiler.values.ValueSet;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.EnumSet;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Objects;
import java.util.SequencedMap;
import java.util.Set;
import java.util.function.Function;

/**
 * One assignment of some numbers that a region admits, or nothing.
 *
 * <p>A number is a position's, or one taken over the values standing at a position — what the
 * elements of a container add up to. Both are chosen here as places on their order, and what
 * comes to a number of the second kind is composed afterwards, where its location is.
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
     * Where each of {@code terms} may stand together inside {@code within}, with nothing asked of
     * the assignment beyond the region admitting it.
     */
    static Standing of(SearchRegion within, List<? extends NumericTerm> terms,
                       Function<NumericTerm, Carrier> on, WitnessSearch looking) {
        return of(within, terms, on, looking, Composing.ANY_ASSIGNMENT);
    }

    /**
     * Where each of {@code terms} may stand together inside {@code within} and a row can be composed
     * with them standing there, or what this found out about there being no such assignment.
     *
     * @param on        what each position is counted on, or null for one this has no order for —
     *                  which is a position no value is chosen at here, and the whole assignment is
     *                  refused rather than made without it
     * @param looking   what the declarations leave each position and what one crossing of such a
     *                  set with a run may cost. Both, and from the one place that pairs them: a
     *                  search given the sets alone would have to reach for an allowance, and what it
     *                  reached for would be a budget nothing granted it
     * @param composing asked of every assignment the region admits, once every number of it stands
     *                  somewhere
     */
    static Standing of(SearchRegion within, List<? extends NumericTerm> terms,
                       Function<NumericTerm, Carrier> on, WitnessSearch looking,
                       Composing composing) {
        // What the rules settle about the question, before any of it is looked for. Two ways for
        // them to settle it and both are the region as it was handed over: it may admit no
        // assignment at all, and it may admit one while leaving a position the question names
        // nowhere to stand. The second is not the first — an input holding an empty collection is a
        // value, and a position inside that collection has no value — and a walk that met either of
        // them would spend what it is allowed on values the rules refuse and come back naming a
        // figure.
        if (leavesTheQuestionNothing(within, terms)) {
            return new Standing.ProvedImpossible();
        }
        SequencedMap<NumericTerm, Place> standing = new LinkedHashMap<>();
        Met met = new Met();
        if (walk(within, terms, 0, on, looking, composing, standing, met)) {
            return Standing.Found.walked(standing);
        }
        return met.settlesTheQuestion()
                ? new Standing.ProvedImpossible()
                : new Standing.NotFound(met.shortfall());
    }

    /**
     * Whether a row can be composed with every number of an assignment standing where it does.
     *
     * <p><b>Asked of the whole assignment and not of a number as it is placed.</b> Which value is
     * composed where a location is depends on every number standing there — how many a list holds
     * and what its elements add up to are built as one list, which neither of them alone is — so a
     * number asked about before the rest of its location is placed is asked a question the row
     * never puts.
     *
     * <p>What the region admits is a necessary condition and this is the rest of it: a number the
     * rules leave a value is not a number some value of the input comes to, and a walk that took the
     * first for the second offers a row at a number nothing builds.
     */
    @FunctionalInterface
    interface Composing {

        /** Every assignment the region admits, as a caller that composes nothing from it asks. */
        Composing ANY_ASSIGNMENT = _ -> new Composed.Built();

        /** What composing a row with {@code standing} came to. */
        Composed composes(SequencedMap<NumericTerm, Place> standing);
    }

    /**
     * What composing a row with one assignment came to.
     *
     * <p>A row was composed, the rules were shown to leave the assignment no value, or neither. The
     * second is about the model and the third about what this compiler built: what it fell short of
     * on the way travels beside it as one value ({@link CompositionShortfall}), empty where the
     * values it wrote were refused and filled where a figure was reached or a population written in
     * part. A case per vocabulary would have every reader decide again which of them it had.
     */
    sealed interface Composed {

        /** A row was composed. */
        record Built() implements Composed {}

        /**
         * The rules leave no value at the assignment: what composing it showed, and not that
         * composing it stopped.
         */
        record Refuted() implements Composed {}

        /** No row was composed, and this is what of this compiler's the composing met. */
        record NotBuilt(CompositionShortfall met) implements Composed {}
    }

    /**
     * What every assignment the walk did not take met, gathered over the whole walk: the figures
     * that stopped it, the values it could not hold, what composing a row with each assignment the
     * region admitted fell short of — and whether every one of them was shown to have no value, the
     * walk having been through every value the region admits.
     */
    private static final class Met {

        private final Set<CompositionBudget> figures = EnumSet.noneOf(CompositionBudget.class);
        private final Set<CompositionCapacity> unheld = new HashSet<>();
        private CompositionShortfall composing = CompositionShortfall.NONE;
        // Whether some assignment was shown to have no value, whether some was refused without
        // being shown, and whether some number's values were left unwalked — by a figure, by an
        // order with no step, or by there being nothing to read the number on.
        private boolean refuted;
        private boolean notBuilt;
        private boolean leftUnwalked;

        CompositionShortfall shortfall() {
            return CompositionShortfall.of(figures, Set.of(), unheld).and(composing);
        }

        /**
         * Whether what the walk met shows the rules leave the question nothing: every value the
         * region admits walked, and every assignment of them shown to have no value.
         */
        boolean settlesTheQuestion() {
            return refuted && !notBuilt && !leftUnwalked && shortfall().nothing();
        }
    }

    /**
     * Whether {@code within} settles that {@code terms} have no assignment in it before any value
     * is chosen: it admits none at all, or leaves one of them nowhere to stand.
     *
     * <p>The region's proof and nothing walked, so a caller holding a region narrower than the
     * question — one an earlier choice was given to — asks it again of the region the question is
     * about.
     */
    static boolean leavesTheQuestionNothing(SearchRegion within,
                                            List<? extends NumericTerm> terms) {
        return within.emptiness().isPresent() || leavesNothing(within, terms);
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
                                         List<? extends NumericTerm> terms) {
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
                Set<NumericTerm> seen = new HashSet<>();
                for (Placed each : this.inFixingOrder) {
                    if (!seen.add(each.term())) {
                        throw new IllegalArgumentException(
                                "a number is placed once: " + each.term());
                    }
                }
            }

            /** What the walk came to, its numbers in the order it fixed them. */
            private static Found walked(SequencedMap<NumericTerm, Place> standing) {
                List<Placed> placed = new ArrayList<>();
                standing.forEach((term, place) -> placed.add(new Placed(term, place)));
                return new Found(placed);
            }

            /** One number and the place the walk put it at. */
            record Placed(NumericTerm term, Place place) {

                public Placed {
                    Objects.requireNonNull(term, "a place is a number's");
                    Objects.requireNonNull(place, "a number is placed somewhere");
                }
            }

            /** The numbers and where each stands, in the order the walk fixed them. */
            List<Placed> inFixingOrder() {
                return inFixingOrder;
            }

            /** Where {@code term} stands, or null where this places no such number. */
            Place placeOf(NumericTerm term) {
                for (Placed each : inFixingOrder) {
                    if (each.term().equals(term)) {
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
         * <p>Shown one of two ways, and no figure travels with either. The region leaves the
         * question no assignment, which is there before any value is chosen; or the walk went
         * through every value the region admits, and composing a row with each assignment of them
         * showed the rules leave it no value. Not where one of them was refused without that
         * being shown, or some value was left unwalked: a value nothing showed has none is one a
         * longer search may build at.
         */
        record ProvedImpossible() implements Standing {}

        /**
         * Nothing was found, and nothing follows about whether an assignment exists.
         *
         * <p>{@code met} is what of this compiler's the walk and the composing of each assignment it
         * reached fell short of, and it is empty as readily as not — a walk that tried everything it
         * had to try is not a walk that walked everything there is. One value for all of it, so a
         * caller that says why nothing was found says every part of it.
         */
        record NotFound(CompositionShortfall met) implements Standing {

            public NotFound {
                Objects.requireNonNull(met, "a walk that found nothing says what it met, or none");
            }
        }
    }

    /**
     * The walk from one position on, with the ones before it fixed in {@code within}.
     *
     * <p>Depth-first, and the region is narrowed as each is chosen rather than at the end: a value
     * that leaves the rest nothing is stepped past here, where there is still another to try, and
     * not reported once every position has been given one.
     *
     * <p>And an assignment the region admits is taken only where a row is composed with it. Asked
     * once every number stands somewhere ({@link Composing}), and one that comes to nothing is
     * stepped past as a value the rules refuse is: the last number tries its next value, and past
     * it the one before.
     */
    private static boolean walk(SearchRegion within, List<? extends NumericTerm> terms,
                                int at,
                                Function<NumericTerm, Carrier> on,
                                WitnessSearch looking,
                                Composing composing,
                                SequencedMap<NumericTerm, Place> standing,
                                Met met) {
        if (at == terms.size()) {
            return switch (composing.composes(standing)) {
                case Composed.Built _ -> true;
                case Composed.Refuted _ -> {
                    met.refuted = true;
                    yield false;
                }
                case Composed.NotBuilt(CompositionShortfall shortOf) -> {
                    met.notBuilt = true;
                    met.composing = met.composing.and(shortOf);
                    yield false;
                }
            };
        }
        NumericTerm term = terms.get(at);
        Carrier carrier = on.apply(term);
        if (carrier == null) {
            met.leftUnwalked = true;
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
            // Nothing read of where the term runs, and nothing walked of it.
            case null -> {
                met.leftUnwalked = true;
                return false;
            }
        }
        if (runs == null) {
            met.leftUnwalked = true;
            return false;
        }
        // The three narrowings this position stands under, read once and handed to the walk whole.
        // What the arithmetic leaves the number is one of them; the walk is held to the other two
        // at every place it reaches, and not only at the one it starts from.
        ValueSet admits = admittedAt(term, looking, within);
        PlacesApart apart = apartAt(term, within);
        Place first = carrier.somethingOtherThan(apart, runs, admits, looking.meter());
        if (first == null) {
            met.leftUnwalked = true;
            return false;
        }
        // A value held to a class is a value of the class, so its members are what is walked, in
        // the order a walk outward from the same place takes: a step of one reaches a member only by
        // luck, and every value between two members is one the rules refuse.
        HeldClass held = term instanceof NumericTerm.ValueOf value
                ? within.classAt(value) : HeldClass.NONE;
        if (!(held instanceof HeldClass.None) && held.countsOn(carrier)
                && Count.number(first).exactly().floor()
                        instanceof ExactAnswer.Held<BigInteger> from) {
            ClassMembers inside = held.nearest(from.value(), runs, VALUES_A_POSITION_IS_TRIED_AT);
            for (Place tried : inside.notApart(apart)) {
                if (carrier.admitted(admits, tried)
                        && tryingAt(within, term, tried, terms, at, on, looking, composing,
                                standing, met)) {
                    return true;
                }
            }
            if (inside.stoppedShort()) {
                met.leftUnwalked = true;
                met.figures.add(CompositionBudget.VALUES_A_POSITION_ON_THE_WAY_IS_TRIED_AT);
            }
            return false;
        }
        Outwards.Walked walked = Outwards.from(first, Count.of(1), carrier, runs,
                VALUES_A_POSITION_IS_TRIED_AT, PLACES_A_POSITION_IS_LOOKED_AT, admits, apart);
        for (Place tried : walked) {
            if (tryingAt(within, term, tried, terms, at, on, looking, composing, standing, met)) {
                return true;
            }
        }
        // What the walk of this position came to, read over the ways it can end rather than off one
        // of them. Each says something different about an empty hand, and a reading that asked only
        // whether a figure was met said the first of them about all three.
        if (walked.ended() != Outwards.Ended.HAVING_TRIED_THEM_ALL) {
            met.leftUnwalked = true;
        }
        switch (walked.ended()) {
            // Every value this position had to offer was tried and none of them led anywhere.
            case HAVING_TRIED_THEM_ALL -> { }
            // There were more, and a figure of this compiler's is why they were not tried, which is
            // what the caller is owed beside the empty hand. Which figure, because raising one of
            // them tries more of what the walk found and raising the other looks further for
            // something to find, and a reader handed the wrong one raises a number that reaches
            // nothing.
            case AT_THE_FIGURE_OF_CANDIDATES ->
                    met.figures.add(CompositionBudget.VALUES_A_POSITION_ON_THE_WAY_IS_TRIED_AT);
            case AT_THE_FIGURE_OF_PLACES_LOOKED_AT ->
                    met.figures.add(CompositionBudget.PLACES_A_POSITION_ON_THE_WAY_IS_LOOKED_AT);
            // And an order with no step to take, where the one place this named is not the whole of
            // what the position holds. Nothing is recorded, because what was left is a population
            // and what travels from here is figures: an entry made here would tell a reader to raise
            // a number that reaches none of it. Said as the arm it is rather than left to the figure
            // above being false, which is how the same fact was lost at the pair search.
            case WITH_NO_STEP_TO_TAKE -> { }
            // And a place further out this could not hold. No figure reaches past it, so it is not
            // among the figures; it travels in its own vocabulary, with which way it went unheld.
            case AT_A_PLACE_IT_COULD_NOT_HOLD -> met.unheld.add(new CompositionCapacity(
                    CompositionCapacity.Where.VALUES_A_POSITION_ON_THE_WAY_IS_WALKED_TO,
                    walked.unheld()));
        }
        return false;
    }

    /**
     * The term {@code at} held at {@code tried} and the walk of every term after it, or nothing
     * where the rules leave nothing there — which steps on, as a value the rules refuse does.
     */
    private static boolean tryingAt(SearchRegion within, NumericTerm term, Place tried,
                                    List<? extends NumericTerm> terms, int at,
                                    Function<NumericTerm, Carrier> on, WitnessSearch looking,
                                    Composing composing,
                                    SequencedMap<NumericTerm, Place> standing, Met met) {
        SearchRegion next = within.given(term, tried);
        if (next.emptiness().isPresent()) {
            return false;
        }
        standing.put(term, tried);
        if (walk(next, terms, at + 1, on, looking, composing, standing, met)) {
            return true;
        }
        standing.remove(term);
        return false;
    }

    /**
     * What the declarations leave the position {@code term} is read at, or nothing narrowed where
     * it is read at none.
     *
     * <p>A number over a run, or how often a value occurs among a container's elements, is a
     * number of the values standing there and not one of them: a set a position admits says which
     * values may be written at it, and no value is written at such a number. What the rules leave
     * it is the region's, which the walk is held to already. The end of the values of a key is one
     * of the values at its place, so it is admitted no value the place is not.
     */
    private static ValueSet admittedAt(NumericTerm term, WitnessSearch looking,
                                       SearchRegion within) {
        return switch (term) {
            case NumericTerm.FromOnePosition one -> looking.toNarrowBy(one, within);
            // One of the values at its place, so none the place does not admit.
            case NumericTerm.ExtremeOfItsKey extreme ->
                    looking.toNarrowBy(extreme.valuesTakenFrom(), within);
            case NumericTerm.TakenOver _, NumericTerm.Multiplicity _,
                 NumericTerm.OccurrencesOfItsValue _, NumericTerm.OccurrencesOfAKey _ ->
                    ValueSet.ANY;
        };
    }

    /** The places {@code within} holds the position {@code term} is read at away from, or none
     *  where it is read at none ({@link #admittedAt}). */
    private static PlacesApart apartAt(NumericTerm term, SearchRegion within) {
        return switch (term) {
            case NumericTerm.FromOnePosition one -> within.apartAt(one);
            case NumericTerm.TakenOver _, NumericTerm.Multiplicity _,
                 NumericTerm.OccurrencesOfItsValue _, NumericTerm.OccurrencesOfAKey _,
                 NumericTerm.ExtremeOfItsKey _ -> PlacesApart.NONE;
        };
    }

    private NumericWitness() {}
}
