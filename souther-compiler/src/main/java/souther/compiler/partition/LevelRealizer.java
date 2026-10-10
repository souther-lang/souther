package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.NumericTerms;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.numeric.AdditiveImage;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.UnheldNumber;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.OrderedInterval;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.PlacesApart;
import souther.compiler.numeric.Rel;
import net.unit8.notation199x.pattern.Meter;
import souther.compiler.values.ValueSet;
import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.EnumSet;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Supplier;

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
 * <p>No search here decides that an item cannot be reached. A refusal is a refusal of what was
 * tried, and {@link Realization} keeps that apart from a proof: read as one, a search that ran out
 * said the model refuses an edge it merely could not compose (ADR-0091). What does decide it are the
 * proofs the rules themselves make, and they are asked for before anything is looked for — a region
 * shown to hold nothing, and a region that leaves the item's quantity no value the item asks for
 * ({@link StandingImpossibility}). A walk of the whole of what is left is the third, and the only
 * one of the three a search has any part in.
 */
public final class LevelRealizer {

    /**
     * Where the positions have to stand for a row to be at this item, or why this found nowhere.
     *
     * <p>The region is handed in per item and is no part of this. Where a row may be written depends
     * on what the rules a row has to pass before it reaches this item leave, which is a fact about
     * where the item's rule is written rather than about the behavior — held here, one region would
     * answer for every item of a body and the search for a border deep in it would run over values
     * nothing arriving there can hold.
     *
     * @param within where a row for this item may be written. Never wider than what the declarations
     *               leave and never narrower than what reaches the item, which is what makes an
     *               exhausted walk of it a proof
     */
    public Realization realize(Standing standing, SearchRegion within,
                               WitnessSearch looking) {
        return realize(standing, within, looking, ValuesTried.NONE);
    }

    /**
     * The same, leaving out the places this point was already composed at.
     *
     * <p>Asked again because the row a place was built into did not stand at the point, which is
     * the one thing that answers it and is settled after this has returned. So what comes back is a
     * candidate and not a witness, and a caller that reads it as one has stopped at the first place
     * the region admits.
     *
     * <p>The exclusions are the caller's and are not kept here. A search that remembered what it
     * had offered would answer differently on two askings of one question, and what it had offered
     * would outlive the point it was offered for.
     */
    public Realization realize(Standing standing, SearchRegion within,
                               WitnessSearch looking, ValuesTried tried) {
        if (within == null) {
            throw new IllegalArgumentException(
                    "a search looks inside a region, and there is always one: an item nothing on the"
                            + " way to it narrows is searched for in what the declarations leave,"
                            + " which is an answer and not an absence");
        }
        // The other vocabulary a position is read in, and it is not optional either. A search that
        // may be handed none is a search that composes without asking what the position holds,
        // which is how a boundary came to be offered a value the declarations refuse.
        if (looking == null) {
            throw new IllegalArgumentException(
                    "a value is composed at a position, and what that position admits is an answer"
                            + " the reading already has: a search that may be handed none is one"
                            + " that composes without asking");
        }
        // Where every position the item names runs in this region, read once and here.
        //
        // <p>Two ways for the rules to settle the item before anything is looked for, and this is
        // both of them. The region may admit no assignment — the rules a row passes on the way can
        // close it between them — and it may admit one while leaving a position the item names
        // nowhere to stand, which an input holding an empty collection does to every position
        // inside it. Either way no place a walk of it reaches is a row, and a walk would end at a
        // figure of this compiler's with nothing to show: a proof about the model reported as this
        // compiler falling short, which is the one thing a reader may act on arriving as one of the
        // things they may not (ADR-0091).
        //
        // <p>Read here rather than where each search wants it, so that there is one reader of it and
        // the searches below are handed ranges. Asked again down there, the answer that is not a
        // range would have to be turned into something a range-shaped reader could hold — which is
        // the collapse this whole class of defect is.
        Map<NumericTerm, NumericDomain.Bounds> runs = new LinkedHashMap<>();
        if (within.emptiness().isPresent()) {
            return new Realization.Impossible();
        }
        // The item's own quantity, asked of the region before its positions are. A rule spanning
        // two of them leaves a fact about the pair, and every position can run somewhere while what
        // they come to between them runs nowhere — or runs somewhere, and nowhere the item asks
        // for, which is what the rules on the way to a border and the border itself say between
        // them. Neither is readable off the positions one at a time.
        if (StandingImpossibility.provesImpossible(within, standing)) {
            return new Realization.Impossible();
        }
        for (NumericTerm term : termsOf(standing)) {
            switch (within.projectionOf(term)) {
                case NumericDomain.FormProjection.Within(NumericDomain.Bounds held) ->
                        runs.put(term, held == null ? NumericDomain.Bounds.OPEN : held);
                case NumericDomain.FormProjection.NothingIsLeft _ -> {
                    return new Realization.Impossible();
                }
                case null -> runs.put(term, NumericDomain.Bounds.OPEN);
            }
        }
        return switch (standing) {
            case Standing.OfOneCoordinate one -> ofOne(one, within, runs, looking, tried);
            case Standing.OfTwoOnOneCarrier two -> ofTwo(two, within, runs, looking, tried);
            case Standing.OfAForm over -> ofAForm(over, within, runs, tried);
            case Standing.OfACount count -> ofACount(count, within, looking, tried);
            case Standing.OfACountAndAForm both ->
                    ofACountAndAForm(both, within, runs, looking, tried);
        };
    }

    /**
     * A count the item asks the sum of, with a form of the input's numbers added to it, and a
     * place for each number of the form and for each number the statement reads beside an element.
     *
     * <p>The count and the form are met together: a count is chosen, the form is asked to come to
     * what is left of the level, and the numbers that come of it are fixed before the elements are
     * chosen against them. Which counts to try is the same {@link #ofACount} walks, from none up;
     * a level is reached by many of them and by none, and which a row is built at is the first
     * that a place can be found for.
     *
     * <p>Never a proof. That no count and no place of the form add up to the level is no
     * statement about the counts the walk did not look at, so the walk that finds none leaves the
     * item open, as a form does when the walk of it is spent.
     */
    private Realization ofACountAndAForm(Standing.OfACountAndAForm over, SearchRegion within,
                                         Map<NumericTerm, NumericDomain.Bounds> runs,
                                         WitnessSearch looking, ValuesTried tried) {
        RealizationTarget.ACount counted = new RealizationTarget.ACount(over.count());
        List<Map.Entry<RealizationTarget.OfANumber, ExactRatio>> terms = new ArrayList<>();
        for (Map.Entry<NumericTerm, ExactRatio> each : AffineReading.ordered(over.form())) {
            terms.add(Map.entry(RealizationTarget.of(each.getKey()), each.getValue()));
        }
        Set<CompositionBudget> stoppedBy = EnumSet.noneOf(CompositionBudget.class);
        Set<CompositionCapacity> unheld = new HashSet<>();
        LevelCandidateSource.Offered offered =
                LevelCandidateSource.forItem(over.where(), over.levels());
        if (offered.stoppedShort()) {
            stoppedBy.add(CompositionBudget.LEVELS_A_SIDE_IS_ASKED_AT);
        }
        int most = CompositionBudget.ELEMENTS_A_COUNT_IS_COMPOSED_WITH.maximum();
        for (Level level : offered.levels()) {
            for (int many = 0; many <= most; many++) {
                // What the form is left to come to once this many elements are counted.
                if (!(level.asAnExactNumber().minus(ExactRatio.of(many))
                        instanceof ExactAnswer.Held<ExactRatio>(ExactRatio rest))) {
                    unheld.add(new CompositionCapacity(
                            CompositionCapacity.Where.COUNTS_AN_ITEM_IS_TRIED_AT,
                            UnheldNumber.NO_REPRESENTATION_EXISTS));
                    continue;
                }
                Search search = new Search(terms, over.on(), within, runs, tried);
                Reached reached = search.solve(rest);
                stoppedBy.addAll(search.stoppedBy());
                unheld.addAll(search.unheld());
                if (reached != Reached.FOUND) {
                    continue;
                }
                Map<RealizationTarget, Place> fixing = new LinkedHashMap<>(search.fixing());
                SearchRegion placed = within;
                for (Map.Entry<RealizationTarget, Place> each : fixing.entrySet()) {
                    if (each.getKey() instanceof RealizationTarget.OfANumber number) {
                        placed = placed.given(number.term(), each.getValue());
                    }
                }
                switch (over.count().placesBeside(placed, many > 0, looking)) {
                    case NumericWitness.Standing.Found beside -> {
                        fixing.put(counted, Count.of(many));
                        for (NumericWitness.Standing.Found.Placed each : beside.inFixingOrder()) {
                            if (!each.position().subjectPath().insideAContainer()) {
                                fixing.putIfAbsent(RealizationTarget.of(each.position()),
                                        each.place());
                            }
                        }
                        Realization made = found(fixing, within, tried);
                        if (made instanceof Realization.Found) {
                            return made;
                        }
                    }
                    case NumericWitness.Standing.ProvedImpossible _ -> { }
                    case NumericWitness.Standing.NotFound(var figures, var held) -> {
                        stoppedBy.addAll(figures);
                        unheld.addAll(held);
                    }
                }
            }
        }
        // The counts past the last tried are counts left untried, and no proof about them.
        stoppedBy.add(CompositionBudget.ELEMENTS_A_COUNT_IS_COMPOSED_WITH);
        return Realization.Unknown.leftOpen(
                Realization.Unknown.Reason.THE_SEARCH_LEFT_SOMETHING_UNTRIED,
                stoppedBy, Set.of(), unheld);
    }

    /**
     * A count the item asks for, and a place for each number the statement reads beside an
     * element.
     *
     * <p>Not which elements. A count is met by many containers, and which of them a row holds is
     * the composing's choice ({@link CardinalityComposer}); a count and the numbers beside it are
     * what a row is asked to be built at, and the numbers are numbers of the row and are put to
     * the rules as any item's are. Which counts to try is {@link LevelCandidateSource}'s, as it is
     * for any item.
     *
     * <p>The numbers beside an element are placed together, with an element meeting the statement
     * where the count is one or more ({@link CountedElements#placesBeside}).
     *
     * <p>Never a proof. That no container holds so many elements meeting the statement is not
     * something a walk over counts settles: the elements are the composing's to choose, and a count
     * nothing here composed is a count left open — even where no element the region leaves meets
     * the statement, since the region was narrowed by the statement here and not by the rules.
     */
    private Realization ofACount(Standing.OfACount count, SearchRegion within,
                                 WitnessSearch looking, ValuesTried tried) {
        RealizationTarget.ACount counted = new RealizationTarget.ACount(count.count());
        Set<CompositionBudget> stoppedBy = java.util.EnumSet.noneOf(CompositionBudget.class);
        Set<CompositionCapacity> unheld = new HashSet<>();
        LevelCandidateSource.Offered offered =
                LevelCandidateSource.forItem(count.where(), count.count().levels());
        if (offered.stoppedShort()) {
            stoppedBy.add(CompositionBudget.LEVELS_A_SIDE_IS_ASKED_AT);
        }
        for (Level level : offered.levels()) {
            // A count is whole and from none, so a level below none is no count at all; one this
            // could not write as a count is a number not held, and said as that.
            Count asked;
            switch (Count.written(level.asAnExactNumber())) {
                case ExactAnswer.Held<Optional<Count>>(Optional<Count> written)
                        when written.isPresent() -> asked = written.get();
                case ExactAnswer.Held<Optional<Count>> _ -> {
                    unheld.add(new CompositionCapacity(
                            CompositionCapacity.Where.COUNTS_AN_ITEM_IS_TRIED_AT,
                            UnheldNumber.NO_REPRESENTATION_EXISTS));
                    continue;
                }
                case ExactAnswer.Unheld<Optional<Count>> notHeld -> {
                    unheld.add(new CompositionCapacity(
                            CompositionCapacity.Where.COUNTS_AN_ITEM_IS_TRIED_AT, notHeld.why()));
                    continue;
                }
            }
            if (asked.at().signum() < 0) {
                continue;
            }
            switch (count.count().placesBeside(within, asked.at().signum() > 0, looking)) {
                case NumericWitness.Standing.Found beside -> {
                    Map<RealizationTarget, Place> fixing = new LinkedHashMap<>();
                    fixing.put(counted, asked);
                    for (NumericWitness.Standing.Found.Placed each : beside.inFixingOrder()) {
                        if (!each.position().subjectPath().insideAContainer()) {
                            fixing.put(RealizationTarget.of(each.position()), each.place());
                        }
                    }
                    Realization made = found(fixing, within, tried);
                    if (made instanceof Realization.Found) {
                        return made;
                    }
                }
                case NumericWitness.Standing.ProvedImpossible _ -> { }
                case NumericWitness.Standing.NotFound(var figures, var held) -> {
                    stoppedBy.addAll(figures);
                    unheld.addAll(held);
                }
            }
        }
        return Realization.Unknown.leftOpen(
                Realization.Unknown.Reason.THE_SEARCH_LEFT_SOMETHING_UNTRIED,
                stoppedBy, Set.of(), unheld);
    }

    /**
     * Every position the item asks a value at: where the item names them in an order, that one,
     * and where it is a form, the order its terms are walked in.
     *
     * <p>Of a count, the numbers its statement reads beside an element and none of the elements'.
     * An element is chosen and not asked to stand anywhere: where the rules leave it nowhere the
     * container holds none, which is a count of none, so the elements' numbers settle nothing here.
     */
    private static List<NumericTerm> termsOf(Standing standing) {
        return switch (standing) {
            case Standing.OfOneCoordinate one -> List.of(one.term());
            case Standing.OfTwoOnOneCarrier two -> List.of(two.on(), two.against());
            case Standing.OfAForm over -> NumericTerms.inOrder(over.form().coefs().keySet());
            case Standing.OfACount count -> count.numbers().stream()
                    .filter(term -> !term.subjectPath().insideAContainer()).toList();
            case Standing.OfACountAndAForm both -> {
                List<NumericTerm> out = new ArrayList<>(NumericTerms.inOrder(
                        both.form().coefs().keySet()));
                both.count().numbers().stream()
                        .filter(term -> !term.subjectPath().insideAContainer()
                                && !out.contains(term))
                        .forEach(out::add);
                yield List.copyOf(out);
            }
        };
    }

    /** One position at a place of its own carrier that the item accepts. */
    private Realization ofOne(Standing.OfOneCoordinate one,
                              SearchRegion within,
                              Map<NumericTerm, NumericDomain.Bounds> runs,
                              WitnessSearch looking, ValuesTried tried) {
        Place at = placeMeeting(one.where(), one.term(), one.of(), runs.get(one.term()),
                looking, tried, Map.of());
        return at == null ? Realization.Unknown.nothingComposedOne()
                : found(Map.of(RealizationTarget.of(one.term()), at), within, tried);
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
     *
     * <p><b>From either position, because a relation has no first coordinate.</b> Which of the two
     * is settled before the other is asked is this search's own arrangement and is no part of what
     * the rule said, so both arrangements are tried and the pair is what either of them reaches. A
     * relation over an order that names a value above any of its own and none below one — which
     * every order over strings is — is composable from the lower position and from neither other
     * way round, so settling the same one of the two always made {@code a < b} answerable and
     * {@code b > a} not.
     */
    private Realization ofTwo(Standing.OfTwoOnOneCarrier two,
                              SearchRegion within,
                              Map<NumericTerm, NumericDomain.Bounds> runs,
                              WitnessSearch looking, ValuesTried tried) {
        // What each reading left behind, in the three vocabularies there are for it. Kept apart
        // all the way here: how a walk ended says which of them it is, and a reader told the wrong
        // one is sent to raise a figure that reached its end or told that no number would have
        // helped where one would.
        java.util.Set<CompositionBudget> stoppedBy =
                java.util.EnumSet.noneOf(CompositionBudget.class);
        java.util.Set<CompositionRepertoire> notAllOf =
                java.util.EnumSet.noneOf(CompositionRepertoire.class);
        Set<CompositionCapacity> unheld = new HashSet<>();
        for (Reading reading : readings(two)) {
            NumericDomain.Bounds settled = runs.get(reading.settles());
            NumericDomain.Bounds together = commonRange(settled,
                    runs.get(reading.anchors()), two.of(), distance(reading.where().anchor()));
            Outwards.Walked walked = alongTheLine(together, two.of(), reading.anchors(),
                    within, looking);
            if (walked == null) {
                // Nothing composed a place to anchor at, which is this reading's own answer and
                // says nothing about how much of the line was looked at.
                continue;
            }
            // How the walk ended, put to the vocabulary that ending belongs to. Read over the
            // endings rather than off a boolean made from them: a walk that met the figure and one
            // that had no step to take are both walks that did not try every place, and told apart
            // only afterwards they were named for each other.
            switch (walked.ended()) {
                case HAVING_TRIED_THEM_ALL -> { }
                case AT_THE_FIGURE_OF_CANDIDATES ->
                        stoppedBy.add(CompositionBudget.PLACES_A_PAIR_IS_TRIED_AT);
                case AT_THE_FIGURE_OF_PLACES_LOOKED_AT ->
                        stoppedBy.add(CompositionBudget.PLACES_A_PAIR_IS_LOOKED_AT);
                case WITH_NO_STEP_TO_TAKE -> notAllOf.add(
                        CompositionRepertoire.PLACES_A_PAIR_IS_TRIED_AT_ON_A_LINE);
                // Neither a figure nor an order without a step: raising a figure reaches no place
                // this could not hold, and the order has a next place. So it is the third
                // vocabulary, with which of the two ways the place went unheld.
                case AT_A_PLACE_IT_COULD_NOT_HOLD -> unheld.add(new CompositionCapacity(
                        CompositionCapacity.Where.PLACES_A_PAIR_IS_WALKED_TO, walked.unheld()));
            }
            for (Place common : walked) {
                // Where the settled one has to stand relative to the anchored one: the place the
                // level's distance from it, and then whatever the item asks of that place.
                // Arithmetic on the carrier's counts and not a walk along it — a walk is an
                // addition that only exists where the order has a smallest step, so a rule over two
                // decimals had no pair anything could compose.
                // Null where the carrier's arithmetic could not put the item's levels beside the
                // place the other position stands at — read on, an item with no level in it was
                // handed to a reader that asks where its level falls.
                // And where this could not hold the place a level moves this one to, this place
                // composed nothing and the next one is tried. Another place or the other reading
                // may compose a pair; where none does, the place not held is said with the answer
                // below, since it is a place this left untried and not one it found empty.
                Related related = relativeTo(reading.where(), common, two.of());
                if (related.unheld() != null) {
                    unheld.add(new CompositionCapacity(
                            CompositionCapacity.Where.PLACES_A_DISTANCE_MOVES_A_POSITION_TO,
                            related.unheld()));
                    continue;
                }
                Criterion here = related.where();
                Place at = here == null ? null
                        : placeMeeting(here, reading.settles(), two.of(), settled, looking, tried,
                                Map.of(RealizationTarget.of(reading.anchors()), common));
                if (at == null) {
                    continue;
                }
                Map<RealizationTarget, Place> fixing = new LinkedHashMap<>();
                fixing.put(RealizationTarget.of(reading.settles()), at);
                fixing.put(RealizationTarget.of(reading.anchors()), common);
                if (found(fixing, within, tried) instanceof Realization.Found made) {
                    return made;
                }
            }
        }
        // Nothing was composed, which is what a pair the ranges leave no place for comes to and
        // what this has always said. What a walk left is said beside that answer rather than in
        // place of it, each in its own vocabulary: raising a figure goes past it, raising anything
        // reaches no second place on an order that has no step, and a place not held is reached by
        // a host with more room or by nothing. The two readings may leave different ones, and all
        // of them go.
        // Which word they come back with is {@link Realization.Unknown#leftOpen}'s to say.
        return Realization.Unknown.leftOpen(Realization.Unknown.Reason.NOTHING_COMPOSED_ONE,
                stoppedBy, notAllOf, unheld);
    }

    /**
     * One way round to search a pair: which position is settled first, and what is asked of it once
     * the other is standing somewhere.
     *
     * <p>The criterion travels with the pair because it is about a quantity, and the quantity is
     * how far one of them stands from the other — which is two quantities for two positions
     * ({@link Criterion#reflected()}). A reading that carried the positions and left the criterion
     * alone would ask the second one for the distance the first one owes.
     *
     * @param settles the position a place is composed for, given where the other one stands
     * @param anchors the position a place is taken for first, from what both of them admit
     */
    private record Reading(NumericTerm.FromOnePosition settles,
                           NumericTerm.FromOnePosition anchors, Criterion where) {}

    /**
     * The ways round to search this pair, in the order they are tried.
     *
     * <p>Both, always, and the first is the one the rule was written as. Which of them reaches a
     * pair is an answer about the order the positions are on and not about the item, so trying only
     * the one that comes to hand is what made the same relation answerable written one way and not
     * the other.
     */
    private static List<Reading> readings(Standing.OfTwoOnOneCarrier two) {
        return List.of(new Reading(two.on(), two.against(), two.where()),
                new Reading(two.against(), two.on(), two.where().reflected()));
    }

    /**
     * How many places along a line a pair is tried at before this stops.
     *
     * <p>Small on purpose. Every place offered here is one the anchored position may stand at, and
     * a pair that is not written at the first few is rarely written further along. What it costs to
     * walk past the places it may not stand at is the other figure's.
     */
    private static final int HOW_MANY_PLACES_A_PAIR_IS_TRIED_AT =
            CompositionBudget.PLACES_A_PAIR_IS_TRIED_AT.maximum();

    /**
     * How many places of that line are walked past to find them.
     *
     * <p>Wider than the figure above, and a figure of its own: what the declarations leave the
     * anchored position and what a rule holds it away from take places out of the middle of the
     * line, and a walk that steps past one of those has not tried a pair there.
     */
    private static final int HOW_MANY_PLACES_A_PAIR_IS_LOOKED_AT =
            CompositionBudget.PLACES_A_PAIR_IS_LOOKED_AT.maximum();

    /**
     * The places to try the pair at, from the one the ranges leave outward.
     *
     * <p>Every place on the line carries the pair as well as any other — where they stand is a
     * witness and the line is the item ({@link Standing.OfTwoOnOneCarrier}) — so one that the rules
     * refuse is one to step off rather than an answer.
     *
     * <p>Which is a distinction the ranges cannot make. A place is chosen from what the two ranges
     * leave and whether it stands is the rules' to say, and a range has no word for a value taken
     * out of the middle of it: before anything narrowed a search, nothing the ranges left was ever
     * refused and the two never disagreed. A region draws one value out and the pair at it is the
     * only pair on the line that cannot be written.
     *
     * <p>One place where the carrier's values do not count. There is no next place to step to, so
     * the one the ranges leave is the whole of what this can name — and the walk says so, because
     * it is not the whole of what the line holds.
     *
     * <p>Null where nothing composed a place to start from, which is this one's own answer and not
     * something to ask a walk about: a walk of no places would have to say whether there were more,
     * and there was never a walk.
     */
    private static Outwards.Walked alongTheLine(NumericDomain.Bounds together, Carrier carrier,
                                                NumericTerm.FromOnePosition anchored,
                                                SearchRegion within,
                                                WitnessSearch looking) {
        // Every narrowing the anchored position stands under, and not the common range alone. What
        // the ranges leave is where the pair can be at all; what the declarations leave that
        // position and what a rule holds it away from are two more, and a place taken from the
        // first and refused by either of the others is a pair reported as one nothing composed.
        //
        // Composed from and not narrowed by, because the place walked here is written into a row.
        // A pair standing at a value out of a set nobody established is the same row this class
        // declines to offer at one position, offered because it was reached through two.
        ValueSet admits = looking.toComposeFrom(anchored).toCrossTheRunWith();
        if (admits == null) {
            return null;
        }
        PlacesApart apart = within.apartAt(anchored);
        Place first = carrier.somethingOtherThan(apart, together, admits, looking.meter());
        return first == null ? null
                : Outwards.from(first, Count.of(1), carrier, together,
                        HOW_MANY_PLACES_A_PAIR_IS_TRIED_AT, HOW_MANY_PLACES_A_PAIR_IS_LOOKED_AT,
                        admits, apart);
    }

    /**
     * The place {@code from} moved by the distance a level names, or null where the carrier holds
     * none there.
     *
     * <p>The distance is a number on the carrier's counts, so this is addition. Where the carrier's
     * values do not count there is no distance to add, and the only level such a quantity takes is
     * the one where the two meet — so the place is the one they meet at and any other level names
     * nothing.
     *
     * <p>Added exactly and put on the carrier only at the end, so a distance no decimal writes
     * reaches the carrier as the number it is and the carrier says there is no value there.
     *
     */
    private static MovedTo movedBy(Place from, Level level, Carrier carrier) {
        ExactRatio apart = distance(level);
        if (!carrier.counts()) {
            return new MovedTo(apart.isZero() ? from : null, null);
        }
        // Where this cannot hold the place the distance moves to, this compiler composed nothing
        // from `from` — never the carrier holding nothing there. The caller trying one place after
        // another is the one that knows what that means, so which of the two this was travels with
        // the answer rather than being told apart by a caught exception.
        return switch (Count.number(from).exactly().plus(apart)) {
            case ExactAnswer.Unheld<ExactRatio> unheld -> new MovedTo(null, unheld.why());
            // And the count put on the carrier: a host with no room to write it out composed
            // nothing from `from` either, and says so the same way.
            case ExactAnswer.Held<ExactRatio> held -> switch (Count.written(held.value())) {
                case ExactAnswer.Unheld<Optional<Count>> unheldCount ->
                        new MovedTo(null, unheldCount.why());
                case ExactAnswer.Held<Optional<Count>> written ->
                        new MovedTo(written.value().map(carrier::onTheGrid).orElse(null), null);
            };
        };
    }

    /** Where a distance moved a place to: the place, or which way the exact arithmetic could not
     *  hold the sum. Neither set is the carrier holding nothing there — that is a place of
     *  {@code null} with no reason, which is not an unheld number and is the ordinary answer this
     *  had before either compose a place or say why not. */
    private record MovedTo(Place place, UnheldNumber unheld) {}

    /**
     * The number a level of the distance between two positions is.
     *
     * <p>Established by every caller: a distance is a number, and a level of it on an order with no
     * numbers reaching here is this compiler having mixed two orders.
     */
    private static ExactRatio distance(Level level) {
        ExactRatio at = level.asANumber();
        if (at == null) {
            throw new IllegalStateException("a distance that is no number: " + level);
        }
        return at;
    }

    /**
     * Every position of a form, at values that put the form where the item asks.
     *
     * <p>Depth-first over the positions, each of them standing where {@link CandidateDomain} says it
     * may: inside the run its own rules leave, and on the coset the coefficients of the rest can
     * land on. Both are facts that settle the position without looking and both are in the set
     * rather than beside it — held as a test applied after choosing, the second one settled nothing
     * wherever the first left a single candidate to choose.
     *
     * <p>Over whole numbers and over decimals alike. A position whose values fill is held to a coset
     * that is dense and is still not every value, so what it can be given is one member of that and
     * never the next one along.
     *
     * <p><b>Three answers, and the difference between them is the point.</b> A walk of a position
     * every value of which could be tried and was proves the level is out of reach; running past the
     * budget, or standing a position somewhere it has more values than this looked at, proves
     * nothing at all (ADR-0091). Reported as one, a search that ran out would take a coverage item
     * away.
     *
     * <p>A side is asked for at the first level past the one it starts from, and then at the next,
     * for as many as {@link LevelCandidateSource} offers. Which levels those are, and how many, is
     * that one's answer: whether a row can be composed at one of them is this one's, and the two are
     * apart so that how long this is willing to look does not read as a fact about the order.
     */
    private Realization ofAForm(Standing.OfAForm over,
                                SearchRegion within,
                                Map<NumericTerm, NumericDomain.Bounds> runs, ValuesTried tried) {
        LevelSpace levels = over.levels();
        // In the form's own order and not the map's. A form is a map, so the order its coefficients
        // were recorded in is a hash order — and which position is solved last decides whether the
        // walk finds an answer inside its budget, so an answer that depended on it would depend on
        // nothing a reader can see.
        List<Map.Entry<RealizationTarget.OfANumber, ExactRatio>> terms = new java.util.ArrayList<>();
        for (Map.Entry<NumericTerm, ExactRatio> each : AffineReading.ordered(over.form())) {
            // Every number is realized by rebuilding one value, so what the walk assigns is a demand
            // and there is one for each term of the form. Whether anything writes such a value is
            // not asked here and is not this reader's to answer: a walk that turned a term away for
            // being of the wrong kind would be deciding what is buildable from the shape of the
            // number, which is the answer that went stale the first time something learned to build
            // one.
            terms.add(Map.entry(RealizationTarget.of(each.getKey()), each.getValue()));
        }
        boolean bounded = true;
        // Every budget any of the level walks ran out of. Collected and not chosen between: two
        // levels stopped by two figures are two things this compiler declined to do, and a reader
        // asking what would let the search go further is owed both.
        java.util.Set<CompositionBudget> stoppedBy =
                java.util.EnumSet.noneOf(CompositionBudget.class);
        Set<CompositionCapacity> unheld = new HashSet<>();
        LevelCandidateSource.Offered offered =
                LevelCandidateSource.forItem(over.where(), levels);
        if (offered.stoppedShort()) {
            stoppedBy.add(CompositionBudget.LEVELS_A_SIDE_IS_ASKED_AT);
        }
        for (Level level : offered.levels()) {
            ExactRatio target = level.asAnExactNumber();
            AtTheLevel here = atTheLevel(over.form(), target, within, runs);
            if (here == null) {
                // The rules leave nothing at this level: a proof about it and about no other.
                continue;
            }
            Search search = new Search(terms, over.on(), here.region(), here.runs(), tried);
            Reached reached = search.solve(target);
            stoppedBy.addAll(search.stoppedBy());
            unheld.addAll(search.unheld());
            if (reached == Reached.FOUND) {
                Realization made = found(search.fixing(), within, tried);
                if (made instanceof Realization.Found) {
                    return made;
                }
                // An assignment the walk reached that no row came of. Nothing about the level
                // follows from it: what refused the row is the writing of it and not the rules the
                // walk held the assignment to.
                bounded = false;
            } else {
                bounded &= reached == Reached.EXHAUSTED;
            }
        }
        // A point asks for one level and a side asks for any level past one, so only the first can
        // be settled by looking: a walk of the whole box that reaches the level nothing else does is
        // a proof, and a side that none of the levels tried reached is a side this stopped looking
        // at.
        if (bounded && over.where() instanceof Criterion.AtTheLevel) {
            return new Realization.Impossible();
        }
        // A side is never settled by looking, so what this comes back with is that something was
        // left untried — which is what it has always come back with, whether or not a figure of
        // this compiler's was reached. The figures are said beside that answer and do not choose
        // it, which is why the answer is not named for one of them running out. Nor for a value it
        // could not hold, which goes beside the figures in its own vocabulary.
        return Realization.Unknown.leftOpen(
                Realization.Unknown.Reason.THE_SEARCH_LEFT_SOMETHING_UNTRIED,
                stoppedBy, Set.of(), unheld);
    }

    /** The region a walk of one level is held to, and where each position runs in it. */
    private record AtTheLevel(SearchRegion region, Map<NumericTerm, NumericDomain.Bounds> runs) {}

    /**
     * The rules with the form's own equation at {@code target} taken in, or null where they are
     * then left nothing.
     *
     * <p>Each position's run is read from a region that carries the equation and the rules it was
     * already held to, so it is narrower wherever a rule relates the positions. A run is a bound
     * and not a set: it can still hold values the other positions cannot complete, which is why
     * the walk puts every whole assignment to the rules at its end. Narrowing, and only for this
     * level: the region is no statement about the side. Where the region cannot carry the
     * equation, the walk is handed what it had.
     */
    private static AtTheLevel atTheLevel(LinearForm<NumericTerm> form, ExactRatio target,
                                         SearchRegion within,
                                         Map<NumericTerm, NumericDomain.Bounds> runs) {
        LinearForm<NumericTerm> equation = new LinearForm<>(target.negated(), form.coefs());
        if (!(within.assuming(equation, Rel.EQ) instanceof SearchRegion.Assumption.Taken(
                SearchRegion narrowed))) {
            return new AtTheLevel(within, runs);
        }
        if (narrowed.emptiness().isPresent()) {
            return null;
        }
        Map<NumericTerm, NumericDomain.Bounds> narrowedRuns = new LinkedHashMap<>();
        for (NumericTerm term : form.coefs().keySet()) {
            switch (narrowed.projectionOf(term)) {
                case NumericDomain.FormProjection.Within(NumericDomain.Bounds held) ->
                        narrowedRuns.put(term, held == null ? NumericDomain.Bounds.OPEN : held);
                case NumericDomain.FormProjection.NothingIsLeft _ -> {
                    return null;
                }
                case null -> narrowedRuns.put(term, NumericDomain.Bounds.OPEN);
            }
        }
        return new AtTheLevel(narrowed, narrowedRuns);
    }

    /** How many assignments the search will try before it stops and says it did not settle it. */
    private static final int STEPS_A_SEARCH_MAY_TAKE =
            CompositionBudget.STEPS_A_SEARCH_MAY_TAKE.maximum();

    /**
     * How many values of a progression nothing bounds are tried.
     *
     * <p>Small on purpose, and it buys something narrower than it looks. The values are already the
     * ones that leave the rest a residue their coefficients land on, so what stepping along it walks
     * past is what the rules take out — and a rule takes values out one region at a time. Nothing
     * here is a proof at any length: a run without an end is not walked to the end.
     *
     * <p><b>Values and not distances.</b> Sixteen of the first is thirty-three of the second where
     * both sides are open, and the two units were mixed here once: this was written as a count of
     * distances and then handed to {@link Outwards}, which counts what it yields. Counted in values
     * for the same reason that one does — it is what a run gives up, and a bound on anything else
     * has to be turned into one before it means anything.
     *
     * <p><b>More than one is needed by models that exist.</b> A disequality takes one value out of
     * the middle of a run without moving either end, so a position carrying one looks unbounded to
     * anything reading ranges and is refused at exactly one place — which is where the coset's own
     * member can land. Cut to one value, {@code a + b = 0} over two positions held away from zero
     * comes back as a search that stopped, and the row at it is one step along.
     *
     * <p>How many past that is not measured. Every progression the suite reaches gives up its row by
     * the second value, and what would ask for a third is a run with two holes in it beside each
     * other.
     */
    private static final int VALUES_A_PROGRESSION_WITHOUT_AN_END_IS_TRIED_AT =
            CompositionBudget.VALUES_OF_AN_UNBOUNDED_PROGRESSION_TRIED.maximum();

    /**
     * What a walk of one position came to.
     *
     * <p><b>Three, because two of them mean opposite things about an empty hand.</b> A position
     * every value of which was tried leaves nothing more to try, and a walk of the whole form that
     * ends this way is what makes {@link Realization.Impossible} a proof. A position that ran on, or
     * that has no next value, leaves the question exactly where it was. Held as one boolean and set
     * from wherever a walk gave up, the two were the same answer and a level nothing reached could
     * not be told from a level nothing looked for.
     */
    private enum Reached {

        /** An assignment of every position, standing where the item asks. */
        FOUND,

        /** Every value there was to try was tried, and none of them was one. A proof. */
        EXHAUSTED,

        /** The walk stopped short of that, and nothing follows from its coming back empty. */
        INCOMPLETE
    }

    /** How often one search reads the declarations again with a position fixed. Each of them is a
     *  reading of every rule reaching the form's positions, and what it buys is skipping
     *  assignments the rules refuse — worth paying for a search that ends quickly and not for one
     *  walking a box a hundred thousand wide. */
    private static final int HOW_OFTEN_THE_RULES_ARE_ASKED_AGAIN =
            CompositionBudget.TIMES_THE_RULES_ARE_ASKED_AGAIN.maximum();


    /** How far a derived end is written out where the division that makes it does not end. Any
     *  number of them is sound while the rounding goes outward; this many keeps the bound close
     *  enough that the walk it bounds is still short. */
    private static final int DIGITS_A_DERIVED_END_KEEPS = 32;

    /**
     * The search itself: an assignment of every position of a form, or nothing.
     *
     * <p>Depth-first over the positions, each of them standing where {@link CandidateDomain} says
     * it may. Both of the things that settle a position without looking are in that set rather than
     * beside it: what the remaining positions can add up to, and what their coefficients can land on.
     * Held as a test the walk applied after choosing, the second one settled nothing wherever the
     * first left one candidate to choose.
     *
     * <p>What a walk comes to is {@link Reached}, and the three answers do not collapse. A position
     * whose values could all be tried and were is what makes an empty-handed walk a proof; one that
     * ran on, or that has no next value to step to, leaves the question open however far it was
     * taken.
     */
    private final class Search {

        private final List<Map.Entry<RealizationTarget.OfANumber, ExactRatio>> terms;
        /**
         * The order each position is read and written on, in the order the terms are walked.
         *
         * <p>One apiece rather than one for the form. Every question the walk asks of an order is
         * about a position — whether its values step, what its next value is, how far it may be
         * moved — and answering them from one order handed to the whole form walked a decimal
         * position over the whole numbers, or the other way about, wherever a form's positions were
         * not written back the same way.
         */
        private final Carrier[] carriers;
        /** Where a row for the item being searched for may be written. */
        private final SearchRegion within;
        /**
         * The assignments a row was already built from that did not stand at the point.
         *
         * <p>Held whole and asked at the end of the walk, which is where an assignment exists. A
         * walk that took one of these out a position at a time would take out every assignment
         * standing that position there, and the ones nothing has tried are most of them.
         */
        private final ValuesTried tried;
        private final Place[] at;
        /**
         * Where each term runs before anything is fixed, worked out once.
         *
         * <p>What the positions from here on can add up to is asked at every step of the walk and
         * of every term still to be chosen, and it is the same answer every time: it is asked of the
         * rules as they stand and not of the rules as this walk has narrowed them. Asked afresh each
         * time, a bounded walk of a wide box pays for a projection per step per term where it used
         * to pay for a lookup.
         */
        private final NumericDomain.Bounds[] runsBetween;
        /**
         * What the positions from each one on can add up to, worked out once.
         *
         * <p>A form names no position twice and weighs none of them by nothing — {@link
         * LinearForm} drops a coefficient the moment it comes to zero — so every
         * suffix of it is a form and has an image.
         */
        private final AdditiveImage[] fromHere;
        private int taken;
        private int asked;
        /** Which budgets of this compiler's this walk ran out of, recorded where each ran out. What
         *  it came back with says that nothing was reached and not what kept it from reaching. */
        private final java.util.Set<CompositionBudget> stoppedBy =
                java.util.EnumSet.noneOf(CompositionBudget.class);
        /** Which values this walk reached and could not hold, recorded where each was met. */
        private final Set<CompositionCapacity> unheld = new HashSet<>();

        java.util.Set<CompositionBudget> stoppedBy() {
            return stoppedBy;
        }

        Set<CompositionCapacity> unheld() {
            return unheld;
        }

        /** Whether there is room for another assignment, marking the budget where there is not. */
        private boolean stepsLeft() {
            if (taken > STEPS_A_SEARCH_MAY_TAKE) {
                stoppedBy.add(CompositionBudget.STEPS_A_SEARCH_MAY_TAKE);
                return false;
            }
            return true;
        }

        Search(List<Map.Entry<RealizationTarget.OfANumber, ExactRatio>> terms,
               Map<NumericTerm, Carrier> on, SearchRegion within,
               Map<NumericTerm, NumericDomain.Bounds> runs, ValuesTried tried) {
            this.tried = tried;
            this.terms = terms;
            this.carriers = new Carrier[terms.size()];
            for (int i = 0; i < terms.size(); i++) {
                carriers[i] = on.get(terms.get(i).getKey().term());
            }
            this.within = within;
            this.at = new Place[terms.size()];
            this.runsBetween = new NumericDomain.Bounds[terms.size()];
            for (int i = 0; i < terms.size(); i++) {
                runsBetween[i] = runs.get(terms.get(i).getKey().term());
            }
            this.fromHere = new AdditiveImage[terms.size()];
            for (int i = 0; i < terms.size(); i++) {
                Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
                for (int j = i; j < terms.size(); j++) {
                    coefs.put(terms.get(j).getKey().term(), terms.get(j).getValue());
                }
                // Each term's own spacing, which is what the image was always asking for: a sum of
                // whole numbers lands on whole numbers, and one decimal among them makes it dense.
                fromHere[i] = AdditiveImage.of(coefs, term -> on.get(term).spacing());
            }
        }

        Reached solve(ExactRatio target) {
            return walk(0, target, within);
        }

        /**
         * Where every position stands, which exists only after a walk that reached a row.
         *
         * <p>Refused otherwise rather than answered with the positions that happen to be fixed. A
         * walk that came back {@link Reached#EXHAUSTED} leaves the ones it gave up on standing
         * nowhere, and a map with nothing under a key is a row somebody is offered with a position
         * missing from it.
         */
        Map<RealizationTarget, Place> fixing() {
            Map<RealizationTarget, Place> out = new LinkedHashMap<>();
            for (int i = 0; i < terms.size(); i++) {
                if (at[i] == null) {
                    throw new IllegalStateException(
                            "a walk that did not reach a row has no assignment to hand over:"
                                    + " nothing stands at `" + terms.get(i).getKey() + "`");
                }
                out.put(terms.get(i).getKey(), at[i]);
            }
            return out;
        }

        /**
         * The walk from one position on, given what the positions before it left owed.
         *
         * <p>The last position is solved and every other is chosen from {@link CandidateDomain}. What
         * comes back says which of the three things happened, and the difference between the last two
         * is the whole reason this is not a boolean: a position all of whose values were tried leaves
         * an empty-handed walk a proof, and one that was cut short leaves it nothing at all.
         */
        private Reached walk(int i, ExactRatio owed,
                             SearchRegion here) {
            taken++;
            if (!stepsLeft()) {
                return Reached.INCOMPLETE;
            }
            ExactRatio coef = terms.get(i).getValue();
            // Where this position runs under what the walk has fixed above it, which is not what it
            // runs in the region the search was handed. The rules leaving it nothing here is a proof
            // about this branch and about no other: the values fixed above took it away, and the
            // walk is standing where it can try a different one. So the branch is exhausted — which
            // is what {@link Reached#EXHAUSTED} says and what a value the rules refuse gets — rather
            // than the item being settled, which would say of every branch what holds of this one.
            NumericDomain.Bounds runs;
            switch (here.projectionOf(terms.get(i).getKey().term())) {
                case NumericDomain.FormProjection.Within(NumericDomain.Bounds held) ->
                        runs = held == null ? NumericDomain.Bounds.OPEN : held;
                case NumericDomain.FormProjection.NothingIsLeft _ -> {
                    return Reached.EXHAUSTED;
                }
                case null -> runs = NumericDomain.Bounds.OPEN;
            }
            // Narrowed by what the positions after this one can add up to. Left at the position's own
            // ends, a box a million wide is walked a million times and the budget runs out on
            // `a + b <= 2000000` — an equation with one answer.
            NumericDomain.Bounds left = leaving(i + 1, owed, coef, runs);
            if (i == terms.size() - 1) {
                return solving(i, owed, coef, left);
            }
            // Where this position may stand: the run, and the values of it that leave the rest a
            // residue their coefficients land on. Both are proofs, and the second is in the set
            // rather than beside it — a residue off what the rest can reach is one no assignment of
            // them arrives at, and a position offering one candidate has nothing for a test applied
            // afterwards to leave.
            CandidateDomain may = CandidateDomain.of(
                    fromHere[i + 1].affinePreimage(coef, owed, carriers[i].spacing()), left);
            return switch (may) {
                case CandidateDomain.None _ -> Reached.EXHAUSTED;
                case CandidateDomain.One only -> trying(i, only.at().at(), owed, coef, here);
                // One value out of a coset whose values fill. There is no next one to step to, so
                // what this walked was never the whole of it however the value turned out.
                case CandidateDomain.Somewhere one ->
                        trying(i, one.at().at(), owed, coef, here) == Reached.FOUND
                                ? Reached.FOUND : Reached.INCOMPLETE;
                case CandidateDomain.Walking every -> walking(i, every, owed, coef, here);
                case CandidateDomain.Outward on -> outward(i, on, owed, coef, here);
                // Neither a proof nor a set: this position's own coset could not be cut to the run
                // at all. Never `EXHAUSTED`, which the rules leaving nothing here is not — this
                // compiler simply could not say what they leave.
                case CandidateDomain.NotWorkedOut it -> {
                    unheld.add(new CompositionCapacity(
                            CompositionCapacity.Where.VALUES_A_POSITION_ON_THE_WAY_IS_WALKED_TO,
                            it.why()));
                    yield Reached.INCOMPLETE;
                }
            };
        }

        /**
         * This position held at one value, and the walk of everything after it.
         *
         * <p>A value the rules are left nothing beside is stepped past here rather than offered and
         * refused where the row is built: refused there, one candidate coming back rejected is
         * reported as every value having been tried. Nothing being left is proved by the rules, so
         * stepping past it takes nothing out of a walk that reaches the end.
         */
        private Reached tryingRatio(int i, ExactRatio x, ExactRatio owed, ExactRatio coef,
                                    SearchRegion here) {
            // A value the host has no room to write out is a value this walk cannot try, which is
            // not a proof the rules leave nothing there: the third vocabulary and `INCOMPLETE`.
            return switch (x.writtenDecimal()) {
                case ExactAnswer.Unheld<Optional<BigDecimal>> unheldValue -> {
                    unheld.add(new CompositionCapacity(
                            CompositionCapacity.Where.VALUES_OF_A_PROGRESSION_WALKED_TO,
                            unheldValue.why()));
                    yield Reached.INCOMPLETE;
                }
                case ExactAnswer.Held<Optional<BigDecimal>> written ->
                        trying(i, written.value().orElse(null), owed, coef, here);
            };
        }

        private Reached trying(int i, BigDecimal x, ExactRatio owed,
                               ExactRatio coef, SearchRegion here) {
            SearchRegion next =
                    narrowing(here, terms.get(i).getKey().term(), x);
            if (next == null) {
                return Reached.EXHAUSTED;
            }
            // A value tried can put what is owed after it out of the exact arithmetic's reach where
            // this position's own value is fine enough. That is never a proof the rules leave
            // nothing here — the walk simply could not go on past this value — so it is the third
            // vocabulary and `INCOMPLETE`, and this value is neither taken nor refused.
            ExactAnswer<ExactRatio> remaining = coef.times(ExactRatio.of(x)).flatMap(owed::minus);
            if (remaining instanceof ExactAnswer.Unheld<ExactRatio> unheldRest) {
                unheld.add(new CompositionCapacity(
                        CompositionCapacity.Where.VALUES_A_POSITION_ON_THE_WAY_IS_WALKED_TO,
                        unheldRest.why()));
                return Reached.INCOMPLETE;
            }
            at[i] = new Count(x);
            Reached reached = walk(i + 1, remaining.orNull(), next);
            if (reached != Reached.FOUND) {
                at[i] = null;
            }
            return reached;
        }

        /**
         * Every value of a run, in order, and what the walk of them all came to.
         *
         * <p>Only this and a position with one value or none can end in a proof. A walk that ends
         * because every value was tried is a proof exactly where each of those values was itself
         * walked to the end, which is why what comes back is the weakest of the children rather than
         * the last of them.
         */
        private Reached walking(int i, CandidateDomain.Walking every, ExactRatio owed,
                                ExactRatio coef,
                                SearchRegion here) {
            // Aligned once, to the wider of the two scales, rather than let every step of what may
            // be a run a hundred thousand wide rescale `by` against `x` on its own: once `first` and
            // `by` share a scale, every further `add` between them holds it and builds no digit to
            // align them. The exact walk below is still what a scale this host cannot align in one
            // decimal falls back to — this is a faster route to the values that arithmetic already
            // proves reachable, not a wider one.
            BigDecimal first = every.first();
            BigDecimal by = every.by();
            int aligned = Math.max(first.scale(), by.scale());
            BigDecimal alignedFirst;
            BigDecimal alignedBy;
            try {
                alignedFirst = first.setScale(aligned);
                alignedBy = by.setScale(aligned);
            } catch (ArithmeticException cannotAlign) {
                return walkingExactly(i, every, owed, coef, here);
            }
            return walkingAtOneScale(i, alignedFirst, alignedBy, every.last(), owed, coef, here);
        }

        /**
         * {@code every}, walked at the one scale {@code first} and {@code by} were aligned to.
         *
         * <p>Every step is a same-scale sum, so no step builds digits to align the two. What a
         * same-scale sum can still meet is a value with more digits than the host holds, and a
         * step that meets one is carried on in exact ratios from the value just tried — which says
         * that value could not be held, the same as a walk that was exact from the start.
         *
         * <p>No step is taken past the last value. The next value after the last is no value of
         * the run, and forming it is work that can only refuse.
         */
        private Reached walkingAtOneScale(int i, BigDecimal first, BigDecimal by, BigDecimal last,
                                          ExactRatio owed, ExactRatio coef,
                                          SearchRegion here) {
            Reached weakest = Reached.EXHAUSTED;
            BigDecimal x = first;
            for (;;) {
                Reached reached = trying(i, x, owed, coef, here);
                if (reached == Reached.FOUND) {
                    return Reached.FOUND;
                }
                if (reached == Reached.INCOMPLETE) {
                    weakest = Reached.INCOMPLETE;
                }
                if (!stepsLeft()) {
                    return Reached.INCOMPLETE;
                }
                if (x.compareTo(last) >= 0) {
                    return weakest;
                }
                try {
                    x = x.add(by);
                } catch (ArithmeticException noRoom) {
                    return onExactly(i, ExactRatio.of(x), ExactRatio.of(by),
                            ExactRatio.of(last), weakest, owed, coef, here);
                }
            }
        }

        /**
         * {@code every}, walked in exact ratios: what a run this host cannot align {@code first}
         * and {@code by} to one scale for falls back to.
         *
         * <p>Worked out exactly and never asked of the two decimals directly: a run whose first and
         * step are ordinary can still meet a next value the exact arithmetic could not hold, and
         * stepping past that one is never a proof the run was walked to the end.
         */
        private Reached walkingExactly(int i, CandidateDomain.Walking every, ExactRatio owed,
                                       ExactRatio coef,
                                       SearchRegion here) {
            ExactRatio x = ExactRatio.of(every.first());
            ExactRatio last = ExactRatio.of(every.last());
            Reached reached = tryingRatio(i, x, owed, coef, here);
            if (reached == Reached.FOUND) {
                return Reached.FOUND;
            }
            Reached weakest = reached == Reached.INCOMPLETE ? Reached.INCOMPLETE : Reached.EXHAUSTED;
            if (!stepsLeft()) {
                return Reached.INCOMPLETE;
            }
            if (x.compareTo(last) >= 0) {
                return weakest;
            }
            return onExactly(i, x, ExactRatio.of(every.by()), last, weakest, owed, coef, here);
        }

        /**
         * The rest of a run after {@code tried}, walked in exact ratios, where {@code weakest} is
         * what the values up to and including {@code tried} came to.
         */
        private Reached onExactly(int i, ExactRatio tried, ExactRatio step, ExactRatio last,
                                  Reached upToTried, ExactRatio owed, ExactRatio coef,
                                  SearchRegion here) {
            ExactRatio x = tried;
            Reached weakest = upToTried;
            for (;;) {
                ExactAnswer<ExactRatio> next = x.plus(step);
                if (next instanceof ExactAnswer.Unheld<ExactRatio> unheldNext) {
                    unheld.add(new CompositionCapacity(
                            CompositionCapacity.Where.VALUES_OF_A_PROGRESSION_WALKED_TO,
                            unheldNext.why()));
                    return Reached.INCOMPLETE;
                }
                x = next.orNull();
                Reached reached = tryingRatio(i, x, owed, coef, here);
                if (reached == Reached.FOUND) {
                    return Reached.FOUND;
                }
                if (reached == Reached.INCOMPLETE) {
                    weakest = Reached.INCOMPLETE;
                }
                if (!stepsLeft()) {
                    return Reached.INCOMPLETE;
                }
                if (x.compareTo(last) >= 0) {
                    return weakest;
                }
            }
        }

        /**
         * A progression nothing bounds, from the value it names outward.
         *
         * <p>Never a proof. What is walked is a run without an end, so an empty-handed walk of as
         * many of its values as this is willing to take says only that those values were not the
         * one.
         *
         * <p>More than one of them, for what the rules can do to a value the arithmetic leaves: the
         * coset says which values leave the rest something they reach, and a rule the region carries
         * can refuse one of those without refusing the next. How many are worth trying is this
         * search's own answer — {@link Outwards} carries the order they are tried in and no
         * allowance of its own, and what a step past a refused value buys is not the same question
         * here as it is for a pair on a line.
         */
        private Reached outward(int i, CandidateDomain.Outward on, ExactRatio owed,
                                ExactRatio coef,
                                SearchRegion here) {
            // The coset is what the arithmetic leaves the position and the run is where the rules
            // leave it; what the declarations leave its values is not given to this search, so
            // there is no set here to narrow by and the identity of that crossing is what goes in.
            // Each value is still put to the region below, which is where a rule that refuses one
            // of them answers.
            Outwards.Walked walked = Outwards.from(new Count(on.from()), new Count(on.by()),
                    carriers[i], on.within(), VALUES_A_PROGRESSION_WITHOUT_AN_END_IS_TRIED_AT,
                    VALUES_A_PROGRESSION_WITHOUT_AN_END_IS_TRIED_AT,
                    ValueSet.ANY, PlacesApart.NONE);
            for (Place x : walked) {
                if (trying(i, Count.number(x).at(), owed, coef, here) == Reached.FOUND) {
                    return Reached.FOUND;
                }
                if (!stepsLeft()) {
                    return Reached.INCOMPLETE;
                }
            }
            // Never a proof either way: a run without an end is not walked to the end, and a walk
            // of every value this had is still a walk of a progression. What the figure adds is
            // only said where the run held one more and this did not take it — added whenever the
            // walk came back empty, it would name a figure over a run that had nothing further in
            // it, which is this compiler claiming to have been stopped where it was not.
            switch (walked.ended()) {
                case HAVING_TRIED_THEM_ALL -> { }
                // One figure named twice, because this walk is given no set and no holes: every
                // place of the run is a place to take, so the looking and the taking are the same
                // number and the reader is owed the same one whichever arm the walk ended on.
                case AT_THE_FIGURE_OF_CANDIDATES, AT_THE_FIGURE_OF_PLACES_LOOKED_AT ->
                        stoppedBy.add(CompositionBudget.VALUES_OF_AN_UNBOUNDED_PROGRESSION_TRIED);
                // A progression is a sum of counts, and a sum exists only over orders that count
                // ({@link LevelSpace#addedUpOver}). So a walk of one that had no step to take is a
                // form over an order with no arithmetic, which is refused before a search is built.
                case WITH_NO_STEP_TO_TAKE -> throw new IllegalStateException(
                        "a progression over an order with no step: " + carriers[i]);
                // Stopped at a value this could not hold, which no figure reaches past: the third
                // vocabulary, with which of the two ways it went unheld.
                case AT_A_PLACE_IT_COULD_NOT_HOLD -> unheld.add(new CompositionCapacity(
                        CompositionCapacity.Where.VALUES_OF_A_PROGRESSION_WALKED_TO,
                        walked.unheld()));
            }
            return Reached.INCOMPLETE;
        }

        /**
         * The last position, solved rather than tried, and every way it can fail is a proof.
         *
         * <p>The division itself is exact. What decides the answer is whether the quotient is a
         * value the position holds: where its values step, a whole number; where they fill, a number
         * a model can write. A third is neither, and what that says is that this prefix has no last
         * value — never that this compiler could not find one.
         *
         * <p>Then the ends themselves, which say whether they are their own values, and then the
         * rules with every position fixed — the one place a whole assignment exists to be held
         * against them. Each of the three refuses on something proved, so a walk that ends here
         * empty-handed has ended.
         */
        private Reached solving(int i, ExactRatio owed, ExactRatio coef,
                                NumericDomain.Bounds left) {
            // The quotient itself can be a value no ratio holds, where what is owed and what this
            // position weighs stand at the two ends of the exponents. That is this walk meeting the
            // arithmetic's own limit, the same as the value below being too fine to write.
            ExactRatio quotient;
            switch (owed.dividedBy(coef)) {
                case ExactAnswer.Held<ExactRatio> held -> quotient = held.value();
                case ExactAnswer.Unheld<ExactRatio> unheldQuotient -> {
                    unheld.add(new CompositionCapacity(
                            CompositionCapacity.Where.VALUES_A_POSITION_ON_THE_WAY_IS_WALKED_TO,
                            unheldQuotient.why()));
                    return Reached.INCOMPLETE;
                }
            }
            BigDecimal solved;
            if (carriers[i].spacing() == souther.compiler.numeric.Granularity.DISCRETE) {
                if (!quotient.isWhole()) {
                    return Reached.EXHAUSTED;
                }
                // Whole, and still one the exact arithmetic can meet no room for: a whole quotient
                // this fine can be one whose digits are past what this host addresses. Not a proof
                // either way, the same as every other place this walk meets the arithmetic's own
                // limit — `INCOMPLETE`, with the third vocabulary saying which value it was.
                switch (quotient.truncated()) {
                    case ExactAnswer.Held<java.math.BigInteger> held ->
                            solved = new BigDecimal(held.value());
                    case ExactAnswer.Unheld<java.math.BigInteger> unheldQuotient -> {
                        unheld.add(new CompositionCapacity(
                                CompositionCapacity.Where.VALUES_A_POSITION_ON_THE_WAY_IS_WALKED_TO,
                                unheldQuotient.why()));
                        return Reached.INCOMPLETE;
                    }
                }
            } else {
                switch (quotient.writtenDecimal()) {
                    case ExactAnswer.Held<Optional<BigDecimal>> written -> {
                        // No decimal is the quotient, so no value of a dense position is.
                        if (written.value().isEmpty()) {
                            return Reached.EXHAUSTED;
                        }
                        solved = written.value().get();
                    }
                    case ExactAnswer.Unheld<Optional<BigDecimal>> unheldQuotient -> {
                        unheld.add(new CompositionCapacity(
                                CompositionCapacity.Where.VALUES_A_POSITION_ON_THE_WAY_IS_WALKED_TO,
                                unheldQuotient.why()));
                        return Reached.INCOMPLETE;
                    }
                }
            }
            // Held against the ends themselves, which say whether they are their own values. A bound
            // of `> 0` leaves one and not zero, and rounding the end to a number first loses which of
            // the two it is.
            if (!left.admits(new Count(solved))) {
                return Reached.EXHAUSTED;
            }
            at[i] = new Count(solved);
            if (!theRulesHaveNotRefused()) {
                at[i] = null;
                return Reached.EXHAUSTED;
            }
            // And not one a row was already built from that did not stand. Stepped past like a
            // value the rules leave nothing beside, and said as a walk that was cut short rather
            // than one that tried everything: what took this assignment away is this compiler
            // having looked, so a walk that gave it up proves nothing about the level.
            if (tried.holds(fixing())) {
                at[i] = null;
                return Reached.INCOMPLETE;
            }
            return Reached.FOUND;
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
        private SearchRegion narrowing(
                SearchRegion here, NumericTerm term,
                BigDecimal at) {
            if (asked >= HOW_OFTEN_THE_RULES_ARE_ASKED_AGAIN) {
                return here;
            }
            asked++;
            SearchRegion next = here.given(term, new Count(at));
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
            java.util.Map<RealizationTarget, Place> all = new LinkedHashMap<>();
            for (int j = 0; j < terms.size(); j++) {
                all.put(terms.get(j).getKey(), at[j]);
            }
            return LevelRealizer.this.theRulesHaveNotRefused(all, within);
        }

        /**
         * The run this position has, narrowed by what the positions after it can add up to.
         *
         * <p>The interval half of where it may stand and not the whole of it. What the rest can add
         * up to is an interval; what this one has to contribute for the residue to land in it is
         * another; both are proofs, so the run is the tighter of them and not the position's own
         * ends. Which values of that run leave the rest a residue their coefficients land on is the
         * other half, and {@link CandidateDomain} is where the two meet.
         *
         * <p>Read off the rules as they stood before anything was fixed. A form's suffix has a run
         * inside the region at hand as well, and it is narrower wherever a rule relates the
         * positions — asking for that one is the change the walk's own cost note argues against, and
         * it is a question of its own rather than part of where a position may stand.
         */
        private NumericDomain.Bounds leaving(int rest, ExactRatio owed, ExactRatio coef,
                                             NumericDomain.Bounds within) {
            ExactRatio[] reach = reach(rest);
            if (reach == null || coef.isZero()) {
                return within;
            }
            // owed - coef * x must lie in [reach0, reach1], so coef * x lies in
            // [owed - reach1, owed - reach0]. Where `owed` and a reach a model's own decimals put
            // far enough apart in scale meet an arithmetic that cannot sum them, this narrows by
            // nothing rather than by a value it cannot hold — the same answer `reach` itself gives
            // for an end nothing bounds.
            ExactRatio oneApart = owed.minus(reach[1]).orNull();
            ExactRatio otherApart = owed.minus(reach[0]).orNull();
            if (oneApart == null || otherApart == null) {
                return within;
            }
            ExactRatio one = oneApart.dividedBy(coef).orNull();
            ExactRatio other = otherApart.dividedBy(coef).orNull();
            if (one == null || other == null) {
                return within;
            }
            ExactRatio low = one.compareTo(other) <= 0 ? one : other;
            ExactRatio high = one.compareTo(other) <= 0 ? other : one;
            Count lowWritten = written(low, java.math.RoundingMode.FLOOR);
            Count highWritten = written(high, java.math.RoundingMode.CEILING);
            if (lowWritten == null || highWritten == null) {
                return within;
            }
            return new NumericDomain.Bounds(
                    Endpoint.lower(within.min(), Endpoint.inclusive(lowWritten)),
                    Endpoint.upper(within.max(), Endpoint.inclusive(highWritten)));
        }

        /**
         * A derived end as a count somebody could write: the number itself where a decimal is it,
         * and rounded the way {@code towards} says where none is.
         *
         * <p><b>Outward and never inward.</b> What this bounds is a proof — a value outside it is one
         * no assignment of the rest completes — so a bound rounded the wrong way takes a value the
         * box holds out of the walk, and a walk that then finds nothing calls the level unreachable.
         * Rounded to sixteen digits at the nearest, {@code a = 10000000000000001} was rounded to
         * {@code 10000000000000000} and the one pair that meets the line was proved not to exist.
         *
         * <p>The division above is exact, so what is left here is only that the interval algebra
         * this end is handed to counts in decimals. A third has none, and the number written out for
         * it is past where the rules stop rather than short of it.
         */
        private static Count written(ExactRatio at, java.math.RoundingMode towards) {
            // No end where the host has no room to write the count out: the end is dropped and the
            // range is wider, which is sound for the reason above.
            if (!(Count.written(at) instanceof ExactAnswer.Held<Optional<Count>> exactly)) {
                return null;
            }
            if (exactly.value().isPresent()) {
                return exactly.value().get();
            }
            BigDecimal outward =
                    at.asDecimal(towards, DIGITS_A_DERIVED_END_KEEPS).orNull();
            return outward == null ? null : new Count(outward);
        }

        /**
         * The least and the greatest the positions from {@code i} on can add up to, or null where
         * one of them is unbounded and there is nothing to say.
         */
        private ExactRatio[] reach(int i) {
            ExactRatio least = ExactRatio.ZERO;
            ExactRatio most = ExactRatio.ZERO;
            for (int j = i; j < terms.size(); j++) {
                NumericDomain.Bounds within = runsBetween[j];
                ExactRatio coef = terms.get(j).getValue();
                ExactRatio low = numberOf(within.min());
                ExactRatio high = numberOf(within.max());
                if (low == null || high == null) {
                    return null;
                }
                ExactRatio one = coef.times(low).orNull();
                ExactRatio other = coef.times(high).orNull();
                if (one == null || other == null) {
                    return null;
                }
                // A model's own ends can be far enough apart in scale, running, that the exact
                // arithmetic cannot carry the product or the sum this narrowing is built from.
                // Nothing to say is already this method's own answer for an end nothing bounds, so
                // an unheld number reads the same way: `leaving` narrows by nothing rather than by
                // a value this cannot hold.
                least = least.plus(one.compareTo(other) <= 0 ? one : other).orNull();
                most = most.plus(one.compareTo(other) <= 0 ? other : one).orNull();
                if (least == null || most == null) {
                    return null;
                }
            }
            return new ExactRatio[] {least, most};
        }

        private static ExactRatio numberOf(Endpoint end) {
            return end == null || !(end.at() instanceof Count count) ? null : count.exactly();
        }

    }

    /** Where {@code where} lands relative to {@code common}, or which way the exact arithmetic could
     *  not hold a level it needed to move — the first such reason met, said instead of the item that
     *  reason stopped {@link #relativeTo} composing. */
    private record Related(Criterion where, UnheldNumber unheld) {}

    /**
     * The item read as a question about one place of one carrier, given where the other position
     * stands.
     *
     * <p>A level of a distance says nothing about a carrier's order until the other end of it is
     * known. Once it is, an item about the pair is an item about one place — which is why the two
     * are searched for by one procedure rather than by two that agreed by being written alike.
     */
    private static Related relativeTo(Criterion where, Place common, Carrier of) {
        // Every level of the item read as the place it lands on once the other end of the line is
        // known. Mapped one level at a time and not by handing one place to all of them: a run has
        // two ends and a line between them, and a mapping that gave them all the same place left a
        // run that said nothing about which side of the line it lay — so a search took whatever the
        // declared domain offered first and a row on the line came back for a point past it.
        // Null where the carrier's arithmetic puts a level nowhere. Which end that happens at
        // decides what it means: a line with no place is an item this order cannot be read as at
        // all, and a run's far end with no place is a run that reaches as far as the carrier does.
        UnheldNumber[] unheld = {null};
        java.util.function.UnaryOperator<Level> onto = level -> {
            MovedTo moved = movedBy(common, level, of);
            if (moved.unheld() != null && unheld[0] == null) {
                unheld[0] = moved.unheld();
            }
            return moved.place() == null ? null : new Level.OnACarrier(of, moved.place());
        };
        Criterion mapped = switch (where) {
            case Criterion.AtTheLevel at -> only(new Criterion.AtTheLevel(onto.apply(at.at())),
                    onto.apply(at.at()));
            case Criterion.Within within -> {
                Band run = within.band().mappedBy(onto);
                yield run == null ? null : new Criterion.Within(run,
                        within.except() == null ? null : onto.apply(within.except()),
                        within.away());
            }
        };
        return new Related(unheld[0] == null ? mapped : null, unheld[0]);
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
    private static Place placeMeeting(Criterion where, NumericTerm.FromOnePosition term,
                                      Carrier carrier, NumericDomain.Bounds bounds,
                                      WitnessSearch looking, ValuesTried tried,
                                      Map<RealizationTarget, Place> given) {
        PlacesApart apart = tried.apartFor(RealizationTarget.of(term), given);
        Place offered = switch (where) {
            // The level itself, and the set is not asked. A point on a line stands where the rule
            // wrote it; held to what the declarations admit, a line drawn at a value they refuse
            // would stop being an item rather than being reported as one nothing can stand at.
            // A level already tried with the rest of them standing where they stand now is not
            // offered again. The rule wrote one place here and a row built from that arrangement
            // did not stand, so there is nothing else to offer under it — said as nothing composed
            // rather than as the same place a second time, which a caller asking again would read
            // as a search that had not moved.
            case Criterion.AtTheLevel at ->
                    apart.has(at.at().asAPlace()) ? null : at.at().asAPlace();
            // Nothing composed where nothing worked out what the position holds. Which is this
            // compiler's own limit and is reported in the word it has for one: a run searched against
            // a set nobody established would offer a row at a position whose rules were never read.
            // A path the reading puts no position at is not that, and the run is what a value there
            // is composed from.
            case Criterion.Within within -> {
                ValueSet admits = looking.toComposeFrom(term).toCrossTheRunWith();
                yield admits == null ? null
                        : someValueIn(within, carrier, bounds, admits, apart, looking::meter);
            }
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
     * A place inside the run this item is, that the position's values take in.
     *
     * <p>The end the item is named for is tried first, in each run in turn. That is what makes the
     * row one beside the boundary rather than one at the far side of the partition, and the item
     * carries which end it is: asked for a second time by a caller, a run could be read from the end
     * it is not named for, which is one decision given from two places.
     *
     * <p>And the values themselves once every one of those ends is refused. Which is the same
     * arrangement {@link Carrier#somethingOtherThan} is under, reached for the same reason: the ends
     * read better in a row than anything worked out of a set, and they are not exhaustive — a run
     * bounded by a rule about one number of the position starts at the one value a rule about another
     * refuses, and nothing about the run says so. The set is crossed with the run rather than asked
     * on its own, so a value it holds inside the run is not lost to whichever value it names first.
     *
     * <p><b>An allowance per crossing, which is why what arrives is the way to get one.</b> An item
     * is a region and a region is as many runs as the rules leave it, so this crosses the set with
     * each of them in turn — and a meter spends down. Shared between the runs, what the first
     * crossing cost would be taken off what the second may spend, and whether a run is answered
     * would follow from where it came in the order they are looked at. Which order that is is a
     * searching policy and no answer about the values ({@link LevelRegion}).
     */
    private static Place someValueIn(Criterion.Within within, Carrier carrier,
                                     NumericDomain.Bounds bounds, ValueSet admits,
                                     PlacesApart apart, Supplier<Meter> allowance) {
        LevelSpace space = LevelSpace.onACarrier(carrier);
        List<LevelInterval> runs = within.runsInside(carrier, bounds.min(), bounds.max());
        for (LevelInterval look : runs) {
            // And not one this point was already tried at. The run's own representative is the
            // cheap answer and stays the first one offered; offered again after the row built from
            // it did not stand, it would be the whole of what a second asking ever reaches, and the
            // search below it would never be asked.
            if (space.witness(look, within.away()).level() instanceof Level.OnACarrier on
                    && carrier.admitted(admits, on.at()) && !apart.has(on.at())) {
                return on.at();
            }
        }
        for (LevelInterval look : runs) {
            OrderedInterval run = runOf(look, carrier);
            Place held = run == null ? null
                    : carrier.somewhereIn(admits, run, apart, allowance.get());
            if (held != null) {
                return held;
            }
        }
        return null;
    }

    /**
     * One run of the levels as a run of the carrier's own places, or null where its ends are not
     * places of the position.
     *
     * <p>Null where an end says how much of the quantity a rule wrote rather than a value of it. Such
     * a run is in the written form's units, and a set of the position's values has nothing to say
     * about a number in them — put to one, the set would be answering about a value nobody holds.
     */
    private static OrderedInterval runOf(LevelInterval look, Carrier carrier) {
        Endpoint low = endOf(look.low(), carrier);
        Endpoint high = endOf(look.high(), carrier);
        boolean lost = (look.low() != null && low == null)
                || (look.high() != null && high == null);
        return lost ? null : new OrderedInterval(low, high);
    }

    /** One end of such a run, or null where it is not a place of the position. */
    private static Endpoint endOf(Bound end, Carrier carrier) {
        if (end == null || !end.at().per().equals(ExactRatio.ONE)) {
            return null;
        }
        return end.at().written() instanceof Level.OnACarrier on && on.of().equals(carrier)
                ? new Endpoint(on.at(), end.inclusive()) : null;
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
     * Where both positions of a line between them can stand, once the level's distance is taken off
     * the first.
     *
     * <p>What proves a row can be written on such a line. The line is where the two positions are
     * equal, so a row on it writes one place at both — and whether one exists is the two positions'
     * ranges read together, which is a question the rules answer without anything being built.
     *
     * <p>Null is not a proof of the opposite. Two ranges that leave no place leave none, and that is a
     * fact about the rules; a range this could not read in full is a range this did not read, and the
     * caller is the one holding whether that happened.
     */
    static NumericDomain.Bounds commonRange(NumericDomain.Bounds on, NumericDomain.Bounds against,
                                            Carrier carrier, ExactRatio apart) {
        NumericDomain.Bounds moved = carrier.counts() ? shifted(on, apart.negated()) : on;
        return new NumericDomain.Bounds(
                Endpoint.lower(moved == null ? null : moved.min(),
                        against == null ? null : against.min()),
                Endpoint.upper(moved == null ? null : moved.max(),
                        against == null ? null : against.max()));
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
    private static NumericDomain.Bounds shifted(NumericDomain.Bounds bounds, ExactRatio by) {
        if (bounds == null) {
            return null;
        }
        return new NumericDomain.Bounds(moved(bounds.min(), by), moved(bounds.max(), by));
    }

    /**
     * An end moved by the distance, or no end where the place it moves to is none this can write.
     *
     * <p>Dropping the end widens the range, and that is sound here: what this bounds is where a
     * search starts looking, and every placement it composes is put back to the rules before it is
     * handed back ({@link #found}). A wider start costs looking and never offers a placement the
     * rules refuse.
     */
    private static Endpoint moved(Endpoint end, ExactRatio by) {
        if (end == null || !(end.at() instanceof Count count)) {
            return end;
        }
        ExactRatio moved = count.exactly().plus(by).orNull();
        if (moved == null) {
            return null;
        }
        // And none where the host has no room to write the count out, for the same reason.
        return switch (Count.written(moved)) {
            case ExactAnswer.Held<Optional<Count>> written ->
                    written.value().map(at -> new Endpoint(at, end.inclusive())).orElse(null);
            case ExactAnswer.Unheld<Optional<Count>> _ -> null;
        };
    }

    /**
     * A placement handed back, or nothing composed where the rules were shown to leave none.
     *
     * <p><b>The one place a placement becomes an answer.</b> What a search may hand back is the same
     * thing whatever it was searching for — one position at a place of its carrier, two of them a
     * distance apart, a form at a level — and each of those was written on its own. Written on its
     * own, each also had to remember the last step, and two of the three did not: a shape whose
     * search is added later inherits the obligation only if there is one place that carries it.
     *
     * <p>What it means is that the rules were not shown to refuse this placement. Not that a value
     * exists — nothing here builds one, and an emptiness nobody proved is not a value proven to
     * exist. What it removes is narrower and is what a search over ranges gets wrong: a placement
     * the rules are already known to refuse, offered as a row and then reported as though the point
     * had nothing at it.
     *
     * <p><b>And the same for an arrangement a row was already built from.</b> A caller that asks
     * again has asked again for a reason, and one handed back what it handed back before spends
     * every value it is allowed on the one arrangement. Each search narrows by what was tried where
     * it can — a carrier is asked for a place away from them, a walk steps past an arrangement it
     * reaches — and this is where that stops being each search's to remember.
     */
    private Realization found(Map<RealizationTarget, Place> fixing,
                              SearchRegion within, ValuesTried tried) {
        if (tried.holds(fixing)) {
            return Realization.Unknown.nothingComposedOne();
        }
        return theRulesHaveNotRefused(fixing, within)
                ? new Realization.Found(fixing)
                : Realization.Unknown.nothingComposedOne();
    }

    /**
     * Whether the rules, with every position of an item fixed at what was chosen, were not shown to
     * leave nothing.
     *
     * <p>Not that a value exists. Nothing here builds one, and an emptiness nobody proved is not a
     * value proven to exist — what settles that is the row itself, where it is built. What this
     * refuses is narrower and is the whole of what a search over ranges gets wrong: an assignment
     * the rules are already known to refuse, offered as a row and then reported as though the point
     * had nothing at it.
     *
     * <p>Of the whole assignment, because that is what an assignment is. A relation between two
     * positions is in neither of their ranges, so a walk that held each of them to its own ends has
     * checked nothing about the pair.
     *
     * <p><b>Places that are not numbers settle nothing here, so a placement made of them is handed
     * back unheld.</b> A rule relating two strings is one the arithmetic has no word for, and what
     * it leaves them is not something this can be asked — so what is promised is that a placement
     * the rules were shown to refuse is not offered, and it is promised where the rules can be asked
     * about the values in it. Anything more would be a claim about an order this reading does not
     * reach.
     */
    private boolean theRulesHaveNotRefused(Map<RealizationTarget, Place> fixing,
                                           SearchRegion within) {
        Map<NumericTerm, Place> standing = new LinkedHashMap<>();
        // A count is no number the region holds a range of; the numbers fixed beside it are.
        fixing.forEach((target, at) -> {
            if (target instanceof RealizationTarget.OfANumber number) {
                standing.put(number.term(), at);
            }
        });
        return standing.isEmpty() || within.given(standing).emptiness().isEmpty();
    }
}
