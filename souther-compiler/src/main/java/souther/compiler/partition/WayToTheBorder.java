package souther.compiler.partition;

import souther.compiler.inputs.EmptyInput;
import souther.compiler.inputs.NameReach;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.Quantity;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.partition.OneOfEach.Step;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.BooleanSupplier;

/**
 * How a row for one border came to be looked for where it is: every condition on the way, in the
 * order the walk met them.
 *
 * <p>An account and not a place. Where a row is looked for is {@link #narrowing(SearchRegion)} and
 * {@link #requirements()} of what the declarations leave, and those are worked out from this
 * whenever somebody needs them — so they cannot come to say different things, because there is only
 * one of them. A pair kept side by side would be values that have to agree and nothing able to check
 * that they do: {@link SearchRegion} answers questions about values and does not say which
 * conditions it was built from, on purpose.
 *
 * <p><b>Three vocabularies, because a condition lands in one of them or in none.</b> What a
 * comparison states is a relation over values and what a fork states is which case a value turned
 * out to be, and neither says the other: a region has no word for a case, and a narrowing orders
 * nothing. The comparisons divide again, because the values a carrier holds are not always numbers:
 * an inequality over a form of them is the arithmetic's, and a position held against a written value
 * on an order that counts nothing is a bound on that order ({@link TakenConstraint}). And a truth
 * of a {@code Bool} position is neither: it is a value, which a region has no order for and a
 * narrowing has no case for ({@link #truths()}). So a search composing a row against this reads
 * them all, and what it still does not represent is {@link #declined()}.
 *
 * <p><b>This is what an answer keeps.</b> A region is a way of asking rather than something that
 * says what it is, and one kept in an answer carries the whole reading of a module's rules — down to
 * the store the reading was made against — into a value two compilations of one source have to
 * compare equal. What a reader of a finished search wants from it is what the way declined, which is
 * here; what a search wants is the region, and a search is where the region is built.
 *
 * <p>What a report may say from this is what the entries say and no more. That some condition was
 * declined does not make the region wider than the rows that reach the border: a condition the
 * arithmetic could not take in may have been implied by the ones it did, or may hold everywhere.
 * What is known is that not everything on the way is represented in it.
 */
public record WayToTheBorder(List<OnTheWay> onTheWay) {

    /** Nothing on the way to take in.
     *
     * <p>Which is a border of a rule that is about the values rather than about a place in a body:
     * an invariant holds wherever a value stands, so there is nowhere for a row to have come from.
     * Said by the empty account rather than by the absence of one. */
    public static final WayToTheBorder UNTOUCHED = new WayToTheBorder(List.of());

    public WayToTheBorder {
        onTheWay = List.copyOf(onTheWay);
    }

    /**
     * Whether a row reaches the border whatever it holds: nothing on the way asks anything of it,
     * and nothing on the way went unread.
     *
     * <p>Which is what makes a value the declarations admit a row at the border. Where something on
     * the way does ask — a comparison taken in, a narrowing, a condition this reading declined — a
     * value the declarations admit may be one no row arriving at the border holds, and what the
     * declarations prove about it is about the position and not about the border.
     */
    public boolean asksNothingOfARow() {
        return onTheWay.stream().allMatch(each ->
                each instanceof OnTheWay.Settled settled && settled.thisWay());
    }

    /**
     * {@code base} narrowed by what of the {@link OnTheWay.TakenIn} entries a region can say, in
     * the order they are written.
     *
     * <p>Three things hold of what comes back, and the first two are {@link SearchRegion}'s own:
     *
     * <pre>what reaches the border ⊆ this ⊆ what the declarations leave</pre>
     *
     * <p>A {@link OnTheWay.Declined} entry never narrows it — it is the record that something on the
     * way is not represented in what comes back. Nor does a {@link OnTheWay.Settled} one, which asks
     * nothing of a row or is a way none takes ({@link #neverComesOut}).
     *
     * <p>And what a {@link OnTheWay.TakenIn} entry asks is what a composer builds a row to meet;
     * the region carries the part of it a region can say, which is settled where the entry is made
     * rather than hoped for here. A relation is that whole; that some element meets something is
     * the container holding one; that every element does is nothing a region says, since a
     * container holding none meets it and a region reads a term inside the elements as one that is
     * there. Nor is the region narrower for each relation: a constraint the rules already hold is
     * taken in again and leaves it where it was. What holds is the one thing a reader of an account
     * acts on — that the region a search runs over admits every row that meets what was taken in.
     */
    public SearchRegion narrowing(SearchRegion base) {
        SearchRegion region = base;
        for (TakenConstraint each : takenIntoTheRegion()) {
            region = each.narrowing(region);
        }
        return region;
    }

    /**
     * What {@link #narrowing} takes into a region, in the order it takes it in: the region a way
     * leaves is the base with each of these taken in, and nothing else.
     */
    public List<TakenConstraint> takenIntoTheRegion() {
        List<TakenConstraint> out = new ArrayList<>();
        for (OnTheWay each : onTheWay) {
            out.addAll(takenInBy(each));
        }
        return List.copyOf(out);
    }

    /**
     * Whether no input takes this way, proved: the walk a composer reads ({@link #along}), with the
     * numbers each condition states taken into {@code declarations} as it goes, so that a way of
     * several is closed where the numbers chosen along it leave nothing, and not only where two
     * conditions ask for two cases.
     *
     * <p>Only a proof: what the region cannot take in leaves it as it was, a walk stopped by a
     * figure proves nothing, and neither does a group of choices closing beside a group that was
     * not looked at. Numbers inside a container are not taken in, since a region reads such a term
     * as the one element there and the way may be about two.
     *
     * <p>{@code takesIn} is asked before each condition is taken into the region, and a condition
     * it refuses is taken in as nothing: the region stays as it was, which proves nothing past it.
     */
    Optional<NoInputTakesIt> takenByNoInput(SearchRegion declarations, BooleanSupplier takesIn) {
        return OneOfEach.walk(onTheWay, numbered(declarations, takesIn),
                CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT,
                CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG)
                instanceof OneOfEach.Walked.Closed<OnTheWay, NoInputTakesIt>(var _, var why)
                ? Optional.of(why) : Optional.empty();
    }

    /** What a way holds together so far, beside what its numbers leave of the input. */
    private record Numbered(HeldTogether held, SearchRegion region) {}

    /** {@link #ASKED_OF_A_ROW}, with what the numbers of each entry leave of {@code declarations}
     *  taken in as well, wherever {@code takesIn} lets one more be. */
    private static OneOfEach.Vocabulary<OnTheWay, Numbered, NoInputTakesIt> numbered(
            SearchRegion declarations, BooleanSupplier takesIn) {
        return new OneOfEach.Vocabulary<>() {

            @Override
            public List<List<OnTheWay>> alternatives(OnTheWay entry) {
                return ASKED_OF_A_ROW.alternatives(entry);
            }

            @Override
            public Set<TermPath> positions(OnTheWay entry) {
                return ASKED_OF_A_ROW.positions(entry);
            }

            @Override
            public Numbered nothing() {
                return new Numbered(ASKED_OF_A_ROW.nothing(), declarations);
            }

            @Override
            public Step<Numbered, NoInputTakesIt> with(Numbered so, OnTheWay entry) {
                if (entry instanceof OnTheWay.Counted counted) {
                    return CountedWays.admits(this, so, counted);
                }
                return switch (takenIn(so.held(), entry)) {
                    case Step.Closed<HeldTogether, Reachability>(var why) ->
                            new Step.Closed<>(new NoInputTakesIt.TheConditionsClash(switch (why) {
                                case Reachability.NothingReaches(var what) ->
                                        new NoInputTakesIt.Clash.TwoAtOnce(what);
                                case Reachability.NothingComesOutThatWay(var condition) ->
                                        new NoInputTakesIt.Clash.NeverComesOutSo(condition);
                                case Reachability.Reaching _, Reachability.NumbersLeaveNone _ ->
                                        throw new IllegalStateException(
                                        "a way taken in closes on why nothing reaches it, and"
                                                + " not on its numbers, which the region says");
                            }));
                    case Step.Held<HeldTogether, Reachability>(var held) -> {
                        SearchRegion region = ofOnePosition(entry) && takesIn.getAsBoolean()
                                ? narrowedBy(so.region(), entry) : so.region();
                        Optional<EmptyInput> empty = region == so.region() ? Optional.empty()
                                : region.emptiness();
                        yield empty.isPresent()
                                ? new Step.Closed<>(new NoInputTakesIt.TheNumbersLeaveNone(
                                        empty.get()))
                                : new Step.Held<>(new Numbered(held, region));
                    }
                };
            }
        };
    }

    /** Whether every position {@code entry} asks about is one value of a run's own, outside every
     *  container. */
    private static boolean ofOnePosition(OnTheWay entry) {
        return ASKED_OF_A_ROW.positions(entry).stream().noneMatch(TermPath::insideAContainer);
    }

    /** {@code region} with what the one entry {@code each} says of a row taken in
     *  ({@link #narrowing}). */
    private static SearchRegion narrowedBy(SearchRegion region, OnTheWay each) {
        for (TakenConstraint taken : takenInBy(each)) {
            region = taken.narrowing(region);
        }
        return region;
    }

    /** What the one entry {@code each} takes into a region, in order ({@link #narrowing}). */
    private static List<TakenConstraint> takenInBy(OnTheWay each) {
        // What a narrowing says on the position's own order, which a region can carry: the
        // cases it leaves out are values no row past it holds.
        if (each instanceof OnTheWay.Narrowed narrowed) {
            return List.copyOf(narrowed.onItsOrder());
        }
        if (each instanceof OnTheWay.TakenIn taken) {
            return switch (taken.demand()) {
                // Taken in, and the region is asked to take it in: an entry here is one the
                // region said it could carry when the walk recorded it.
                case RowDemand.Relational(var relation) -> List.of(relation);
                // That some element meets these says nothing every row past it holds of each
                // element, so the region is narrowed only by the container holding one. What
                // the element meets is composed where the row is.
                case RowDemand.Exists(var _, var _, var holdingOne, var _) ->
                        List.of(holdingOne.constraint());
                // That every element meets these, which a container holding none does. A
                // region reads a term inside the elements as the value of one that is there,
                // so narrowed on, it would leave nothing where the rules leave the element
                // nothing — and the way past an empty container would be proved closed. And
                // the container is not held to holding none either, since elements meeting
                // these are a way past it too.
                case RowDemand.ForAll _ -> List.of();
                // How many elements meet a statement, which is no number a region holds.
                case RowDemand.SoMany _ -> List.of();
                // The values of a form that leave a remainder are a class, which a region holds
                // no run of.
                case RowDemand.OnARemainder _ -> List.of();
                // A statement no composer writes toward, which a region holds nothing of.
                case RowDemand.ForTheRun _ -> List.of();
                // Which of two values stands at a position no region measures. The row is
                // written with it where the row is composed, and the region says nothing of it.
                case RowDemand.ATruth _ -> List.of();
                // Two values being one on no order, which no region measures either.
                case RowDemand.OneValueAtBoth _ -> List.of();
            };
        }
        return List.of();
    }

    /**
     * What has to be true of the parameters for a row to reach the border, off the narrowings the
     * way took in.
     *
     * <p>The other half of what a region is. A region says which numbers a position may hold and has
     * no word for which case a value turned out to be, so a fork on the way lands here — and a
     * composer holding both is holding the whole of what this reading could state.
     *
     * <p>Or nothing, where two narrowings on the way cannot hold together. That is a way no row
     * takes, which is a fact about the model and not something to compose against: read as an
     * absence of requirements, a row would be composed for a border down a path nothing reaches.
     */
    public Requirements.Merge requirements() {
        Requirements out = Requirements.NONE;
        for (OnTheWay each : onTheWay) {
            if (each instanceof OnTheWay.Narrowed narrowed) {
                Requirements.Merge both = out.merge(narrowed.requirements());
                if (!(both instanceof Requirements.Merge.Merged merged)) {
                    return both;
                }
                out = merged.requirements();
            }
        }
        return new Requirements.Merge.Merged(out);
    }

    /**
     * Which value each {@code Bool} position the way read is asked to hold, off the truths it took
     * in — the third of what a row has to be, beside {@link #narrowing} and {@link #requirements}.
     *
     * <p>Or the position asked for both, which is a way no row takes for the reason two narrowings
     * no position holds together are: whichever condition said which, no value is both.
     */
    public TruthsAsked.Merge truths() {
        List<RowDemand.ATruth> asked = new ArrayList<>();
        for (OnTheWay each : onTheWay) {
            if (each instanceof OnTheWay.TakenIn(var _, RowDemand.ATruth truth)) {
                asked.add(truth);
            }
        }
        return TruthsAsked.of(asked);
    }

    /**
     * What the way asks of a row, each where it was taken in. Only some of them narrow a region
     * built from this: what every element meets leaves it as it is, since a container holding none
     * meets it.
     */
    public List<OnTheWay.TakenIn> takenIn() {
        List<OnTheWay.TakenIn> out = new ArrayList<>();
        for (OnTheWay each : onTheWay) {
            if (each instanceof OnTheWay.TakenIn taken) {
                out.add(taken);
            }
        }
        return List.copyOf(out);
    }

    /**
     * The first condition on the way that no row brings out the way the walk went, or empty where
     * every one of them can be.
     *
     * <p>A fact about the model, as two narrowings no position can hold together are
     * ({@link #requirements()}): a border down such a way is one nothing reaches, and a row
     * composed for it would be one for a way no input takes.
     */
    public Optional<OnTheWay.Settled> neverComesOut() {
        for (OnTheWay each : onTheWay) {
            if (each instanceof OnTheWay.Settled settled && !settled.thisWay()) {
                return Optional.of(settled);
            }
        }
        return Optional.empty();
    }

    /** The ones this reading could state in neither vocabulary, which is what a search composing
     *  against both of them still does not represent — inside an alternative as much as beside
     *  one. */
    public List<OnTheWay.Declined> declined() {
        List<OnTheWay.Declined> out = new ArrayList<>();
        for (OnTheWay each : stated()) {
            if (each instanceof OnTheWay.Declined left) {
                out.add(left);
            }
        }
        return List.copyOf(out);
    }

    /**
     * Every condition the way states, in the order it states them: a condition of several ways,
     * and after it what each of its alternatives states, in the order they are kept.
     *
     * <p>The one walk of the way's conditions that goes inside an alternative, so that a reader
     * placing something on the way and a reader asking what it declined go inside it alike. Placed
     * by the conditions on top alone, two conditions inside one alternative and inside another
     * would be at no place of the way, and what came of them in whatever order it was put
     * together in.
     */
    public List<OnTheWay> stated() {
        List<OnTheWay> out = new ArrayList<>();
        stated(onTheWay, out);
        return List.copyOf(out);
    }

    private static void stated(List<OnTheWay> entries, List<OnTheWay> into) {
        for (OnTheWay each : entries) {
            into.add(each);
            switch (each) {
                case OnTheWay.OneOf several ->
                        several.alternatives().forEach(one -> stated(one, into));
                case OnTheWay.Counted counted -> counted.statements().forEach(one -> {
                    stated(one.holding(), into);
                    stated(one.failing(), into);
                });
                // A narrowing's alternatives are the cases it leaves, each made afresh as a
                // narrowing to that case; they state nothing the narrowing did not.
                case OnTheWay.Narrowed _, OnTheWay.Declined _, OnTheWay.TakenIn _,
                     OnTheWay.Settled _ -> { }
            }
        }
    }

    /**
     * This way with each condition of several ways {@code chosen} names taken as every alternative
     * it names, where it stands, and every other left as it is.
     *
     * <p>By the condition and not by where it stands, so that what was chosen along one way is
     * chosen along another that takes the same condition in: a guard below another takes the
     * other's condition in, and a row held past the first along one of its ways is past it along
     * that way wherever it goes next.
     *
     * <p>Every alternative named, all at once. A row held to two alternatives of one condition is
     * held to both: some element of one container meeting a predicate and some element of another
     * meeting its own hold together, and whether two cases of one value do is what reading the way
     * says ({@link Reachability#of}), as for any two conditions on it.
     */
    public WayToTheBorder choosing(Map<OnTheWay, Set<Integer>> chosen) {
        return chosen.isEmpty() ? this : new WayToTheBorder(choosing(onTheWay, chosen));
    }

    private static List<OnTheWay> choosing(List<OnTheWay> entries,
                                           Map<OnTheWay, Set<Integer>> chosen) {
        List<OnTheWay> out = new ArrayList<>();
        for (OnTheWay each : entries) {
            Set<Integer> taken = each.ofSeveralWays() ? chosen.get(each) : null;
            if (taken == null) {
                out.add(each);
            } else {
                for (int alternative : taken) {
                    out.addAll(choosing(each.alternatives().get(alternative), chosen));
                }
            }
        }
        return out;
    }

    /**
     * The positions what {@code entry} asks of a row turns on: the one account of them, which the
     * walk of a way groups its choices by and a reader asking what holding a row to it writes asks
     * as well.
     */
    static Set<TermPath> positionsOf(OnTheWay entry) {
        return ASKED_OF_A_ROW.positions(entry);
    }

    /** The conditions on this way a row is past one of several ways of
     *  ({@link OnTheWay#alternatives}), in the order the walk met them. */
    public List<OnTheWay> severalWays() {
        return onTheWay.stream().filter(OnTheWay::splitsTheWay).toList();
    }

    /**
     * The ways a row past this one may take, each with one alternative of conditions of several
     * ways taken in where it stands ({@link OnTheWay#alternatives}) — or why no row takes any of
     * them, for the cases, the truths or the counts it asks.
     *
     * <p>A narrowing leaving several cases is one of them. The way whole states the cases it
     * leaves, and a row along it is one of those cases, so it is composed along each.
     *
     * <p>Every row past this way is past one alternative of each such condition. Conditions that
     * turn on no position in common are chosen apart ({@link OneOfEach}); the ways handed on are
     * every combination of their open alternatives where the figure lets them all be, and
     * otherwise some of them with the figure that left the rest. A way with no such condition on
     * it is judged by the same walk, as the one way it is.
     */
    OneOfEach.Walked<OnTheWay, Reachability> along() {
        // A way with no count on it is walked as it always was, with the walk's own figures.
        if (stated().stream().noneMatch(OnTheWay.Counted.class::isInstance)) {
            return walked(onTheWay, ASKED_OF_A_ROW);
        }
        return CountedWays.walkedWithCounts(onTheWay, ASKED_OF_A_ROW, WayToTheBorder::walked);
    }

    private static OneOfEach.Walked<OnTheWay, Reachability> walked(
            List<OnTheWay> entries,
            OneOfEach.Vocabulary<OnTheWay, HeldTogether, Reachability> vocabulary) {
        return OneOfEach.walk(entries, vocabulary,
                CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT,
                CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG);
    }

    /**
     * What a way asks of a row as far as whether its conditions hold together: the cases it
     * requires and the truths it asks, which are what two conditions on one way contradict each
     * other in ({@link Reachability#of}), a condition no row brings out the way taken — and how
     * many elements meet each statement it counts, which two conditions asking for counts that
     * leave none in common contradict each other in as well.
     *
     * @param counts what is left of each count asked, by its spelling
     * @param numbers the relations of numbers it has taken in, which statements of one form
     *                leave no point of the line in common
     */
    private record HeldTogether(Requirements requirements, List<RowDemand.ATruth> truths,
                                Map<String, LevelRegion> counts,
                                List<TakenConstraint.Affine> numbers) {

        HeldTogether withRequirements(Requirements required) {
            return new HeldTogether(required, truths, counts, numbers);
        }

        HeldTogether withTruths(List<RowDemand.ATruth> asked) {
            return new HeldTogether(requirements, asked, counts, numbers);
        }

        /**
         * These with what {@code entry} says of numbers held against what the others did, or why
         * no row is where that leaves it none. An entry that states no relation of numbers
         * changes nothing.
         *
         * <p>Only the way's own reading proves this. The search for what no input takes
         * ({@code numbered}) leaves it to the region of the declarations, which says what the
         * same statements leave of the input together with what the declarations hold, and that
         * is the account it reports in.
         */
        Step<HeldTogether, Reachability> relating(OnTheWay entry) {
            if (!(entry instanceof OnTheWay.TakenIn(var _, RowDemand.Relational(
                    TakenConstraint.Affine affine)))) {
                return new Step.Held<>(this);
            }
            // The ones taken in before have not been proved to leave none, since the way was
            // open, so only the statements of this one's form can newly be proved to.
            List<TakenConstraint.Affine> ofItsForm =
                    WhatStatementsOfOneFormDecide.ofTheFormOf(numbers, affine);
            if (WhatStatementsOfOneFormDecide.of(ofItsForm, null).noRowArrives()) {
                return new Step.Closed<>(new Reachability.NumbersLeaveNone(ofItsForm));
            }
            List<TakenConstraint.Affine> stated = new ArrayList<>(numbers);
            stated.add(affine);
            return new Step.Held<>(new HeldTogether(requirements, truths, counts, stated));
        }

        /** These with the count {@code counted}, one {@link AStatementAtARow#countIn} answers,
         *  asked to be in {@code region}, or why no row is where that leaves it none. */
        Step<HeldTogether, Reachability> counting(Quantity counted, LevelRegion region) {
            LevelRegion left = counts.containsKey(counted.spelled())
                    ? counts.get(counted.spelled()).meet(region) : region;
            if (left.parts().isEmpty()) {
                return new Step.Closed<>(new Reachability.NothingReaches(
                        new Reachability.TwoAtOnce.Counts(AStatementAtARow.elementsOf(counted)
                                .container().inputPosition())));
            }
            Map<String, LevelRegion> out = new LinkedHashMap<>(counts);
            out.put(counted.spelled(), left);
            return new Step.Held<>(new HeldTogether(requirements, truths, out, numbers));
        }
    }

    /** One or more elements, which some element meeting a statement is the count of. */
    private static final LevelRegion ONE_OR_MORE = LevelRegion.of(new LevelInterval(
            Bound.at(new Level.OfTheQuantity(ExactRatio.ONE), true), null));

    /** No element, which every element meeting the denial of a statement is the count of. */
    private static final LevelRegion NONE = LevelRegion.point(new Level.OfTheQuantity(
            ExactRatio.ZERO));

    private static final OneOfEach.Vocabulary<OnTheWay, HeldTogether, Reachability> ASKED_OF_A_ROW =
            new OneOfEach.Vocabulary<>() {

                @Override
                public List<List<OnTheWay>> alternatives(OnTheWay entry) {
                    return entry.ofSeveralWays() ? entry.alternatives() : null;
                }

                @Override
                public Set<TermPath> positions(OnTheWay entry) {
                    return switch (entry) {
                        case OnTheWay.TakenIn taken -> taken.demand().positions();
                        case OnTheWay.Narrowed narrowed -> {
                            Requirements required = narrowed.requirements();
                            Set<TermPath> out = new LinkedHashSet<>(
                                    required.refinements().keySet());
                            for (NameReach.Crossing each : required.crossings()) {
                                out.add(each.at());
                                out.add(each.to());
                            }
                            yield out;
                        }
                        case OnTheWay.Counted counted -> {
                            Set<TermPath> out = new LinkedHashSet<>();
                            counted.parts().forEach(one -> out.addAll(positions(one)));
                            yield out;
                        }
                        case OnTheWay.Settled _, OnTheWay.Declined _, OnTheWay.OneOf _ ->
                                Set.of();
                    };
                }

                @Override
                public HeldTogether nothing() {
                    return new HeldTogether(Requirements.NONE, List.of(), Map.of(), List.of());
                }

                /** {@code so} with {@code entry} taken in, or why no row takes them together. */
                @Override
                public Step<HeldTogether, Reachability> with(HeldTogether so, OnTheWay entry) {
                    if (entry instanceof OnTheWay.Counted counted) {
                        return CountedWays.admits(this, so, counted);
                    }
                    return switch (takenIn(so, entry)) {
                        case Step.Held<HeldTogether, Reachability>(var held) ->
                                held.relating(entry);
                        case Step.Closed<HeldTogether, Reachability> closed -> closed;
                    };
                }
            };

    /** {@code so} with {@code entry} taken in as far as the cases, truths and counts it asks go;
     *  what its numbers say beside the others is {@link HeldTogether#relating}. */
    private static Step<HeldTogether, Reachability> takenIn(HeldTogether so, OnTheWay entry) {
        return switch (entry) {
            case OnTheWay.Settled settled -> settled.thisWay() ? new Step.Held<>(so)
                    : new Step.Closed<>(new Reachability.NothingComesOutThatWay(settled));
            case OnTheWay.Narrowed narrowed -> switch (so.requirements()
                    .merge(narrowed.requirements())) {
                case Requirements.Merge.Merged(Requirements both) ->
                        new Step.Held<>(so.withRequirements(both));
                case Requirements.Merge.Conflict conflict -> new Step.Closed<>(
                        new Reachability.NothingReaches(new Reachability.TwoAtOnce.Cases(conflict)));
            };
            case OnTheWay.TakenIn(var _, RowDemand.ATruth truth) -> {
                List<RowDemand.ATruth> truths = new ArrayList<>(so.truths());
                truths.add(truth);
                yield switch (TruthsAsked.of(truths)) {
                    case TruthsAsked.Merge.Merged _ -> new Step.Held<>(so.withTruths(truths));
                    case TruthsAsked.Merge.Conflict(var at) -> new Step.Closed<>(
                            new Reachability.NothingReaches(new Reachability.TwoAtOnce.Truths(at)));
                };
            }
            case OnTheWay.TakenIn(var _, RowDemand.Exists exists)
                    when exists.counted().isPresent() ->
                    so.counting(exists.counted().get(), ONE_OR_MORE);
            case OnTheWay.TakenIn(var _, RowDemand.ForAll every)
                    when every.counted().isPresent() ->
                    so.counting(every.counted().get(), NONE);
            case OnTheWay.TakenIn(var _, RowDemand.SoMany many) when !many.againstNumbers() ->
                    so.counting(many.count(), many.counts().values());
            // A relation over a number written under a case is a relation of a value that is
            // that case: the number is nowhere else.
            case OnTheWay.TakenIn(var _, RowDemand.Relational relation) -> {
                Requirements required = so.requirements();
                for (NumericTerm term : relation.terms()) {
                    switch (required.merge(term.subjectPath().requirements())) {
                        case Requirements.Merge.Merged(Requirements both) -> required = both;
                        case Requirements.Merge.Conflict conflict -> {
                            yield new Step.Closed<>(new Reachability.NothingReaches(
                                    new Reachability.TwoAtOnce.Cases(conflict)));
                        }
                    }
                }
                yield new Step.Held<>(so.withRequirements(required));
            }
            // A count is judged where its statements are taken in, beside the rest of the way
            // ({@link CountedWays}), and asks nothing of cases or truths on its own.
            case OnTheWay.TakenIn _, OnTheWay.Declined _, OnTheWay.OneOf _,
                 OnTheWay.Counted _ -> new Step.Held<>(so);
        };
    }
}
