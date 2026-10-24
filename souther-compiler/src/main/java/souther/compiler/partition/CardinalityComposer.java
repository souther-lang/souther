package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.Shape;
import souther.compiler.check.TypeView;
import souther.compiler.inputs.ElementKey;
import souther.compiler.inputs.ElementProjection;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Text;
import souther.compiler.numeric.Today;
import souther.compiler.numeric.Towards;
import souther.compiler.numeric.UnheldNumber;
import souther.compiler.numeric.UsualPlace;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;

import java.math.RoundingMode;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.OptionalInt;
import java.util.SequencedMap;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.function.IntFunction;
import java.util.function.IntUnaryOperator;
import java.util.function.Predicate;

/**
 * Containers with so many of their elements meeting each of some statements.
 *
 * <p>What a count asks of a row is elements, and whether an element meets a statement turns on the
 * element's own number and on whatever else the statement reads. The numbers beside an element are
 * fixed before this is asked, as numbers of the row; this chooses elements against them.
 *
 * <p><b>Elements by what they answer.</b> Where each relation over the element turns over is worked
 * out once ({@link AStatementAtARow#turnsAt}). Between two of those places, and at each of them,
 * every relation reads any value the same way, so a value from each is every way an element can
 * answer them. Each value is read for every statement on the container at once, the way a row's
 * element is read, and the values are grouped by what they answer: one group for each way of
 * answering all the statements together. A value a statement could not be read at is neither
 * counted for it nor against it. It goes in no group, and what kept it out is said.
 *
 * <p><b>Then how many of each.</b> A container of so many elements is so many from each group, and
 * it meets every count where the elements of the groups that meet each statement are as many as
 * that count asks. The sizes are walked from none up, and each way of sharing a size out among the
 * groups that meets every count is a container.
 *
 * <p>A list holds one value as often as it likes. A set holds each value once, so a group is drawn
 * on for as many different values as it is asked for, and where it has too few that sharing builds
 * nothing. Which is no proof that no container meets the counts: the values of a group are the
 * ones this named, and a run holds others.
 *
 * <p>Every container is read again as a whole before it is offered. What the groups promise is what
 * each value answered alone, and reading the container is what a row's reading does.
 */
final class CardinalityComposer {

    private static final int MOST_ELEMENTS =
            CompositionBudget.ELEMENTS_A_COUNT_IS_COMPOSED_WITH.maximum();

    private static final int MOST_OFFERED =
            CompositionBudget.CONTAINERS_A_COUNT_IS_OFFERED.maximum();

    private static final int MOST_SHARES =
            CompositionBudget.SHARES_A_COUNT_IS_TRIED_AT.maximum();

    private static final int MOST_COUNTS_OF_KEYS =
            CompositionBudget.COUNTS_OF_KEYS_TRIED.maximum();

    /** Every count of elements: what is asked of a thing the values are grouped by and no count
     *  of which is asked. */
    private static final LevelRegion ANY_COUNT = LevelRegion.of(new LevelInterval(
            Bound.at(new Level.OfTheQuantity(ExactRatio.ZERO), true), null));

    /**
     * Containers of {@code sourceType} meeting every one of {@code counts} at the set {@code
     * demands} asks it for, with some element standing in the set asked of each of {@code
     * standingAt}, and holding as many elements as {@code manyItHolds} is asked for where it is not
     * null.
     *
     * @param together   statements the elements are to meet together, each one of several ways the
     *                   elements may take — which every container composed here meets
     * @param standingAt the element itself, each asked to stand in a set: a value the row places at
     *                   an element, which some element of the container is
     * @param measuring  the orders the input's numbers are counted on, which a number inside an
     *                   element chosen among its values is read at
     * @param within     the region with every number of the row a count's statement reads beside
     *                   an element standing at one value
     */
    static TermRealizations.Realization compose(Type sourceType, List<List<String>> keptApart,
                                                List<RealizationTarget.ACount> counts,
                                                List<RealizationTarget.ElementsMeetingTogether>
                                                        together,
                                                SequencedMap<RealizationTarget, AskedAt> demands,
                                                RealizationTarget.OfANumber manyItHolds,
                                                List<RealizationTarget.OfANumber> standingAt,
                                                Quantities measuring, SearchRegion within,
                                                RuleReadingContext reading) {
        RuleReadingSource ruleSource = reading.source();
        TermPath container = counts.isEmpty() ? together.getFirst().container()
                : counts.getFirst().count().container();
        List<Asked> asked = new ArrayList<>();
        // Each count as the counts it is asked for, and not as the one a row was named at: the
        // item and every condition on the way that ask for it leave a region, and which count of
        // it the container holds is chosen here.
        for (RealizationTarget.ACount each : counts) {
            AskedAt at = demands.get(each);
            if (at == null) {
                return none("nothing says how many elements of `" + container + "` are to meet `"
                        + each + "`");
            }
            asked.add(new Asked.SoManyMeeting(each.count().perElement(), at.about().values(),
                    each.count().differentAt()));
        }
        // Where a count is of the different values the elements meeting a statement hold, every
        // element is chosen apart from the others at that place: then each counts once, and the
        // sharings, which count elements, count the values.
        TermPath apartAt = null;
        for (RealizationTarget.ACount each : counts) {
            TermPath at = each.count().differentAt().orElse(null);
            if (at != null && apartAt != null && !apartAt.equals(at)) {
                return notChosen("the values the elements of `" + container + "` hold are counted"
                        + " at `" + apartAt + "` and at `" + at + "`, and no elements are chosen"
                        + " apart at both");
            }
            apartAt = at != null ? at : apartAt;
        }
        NumericSet size = null;
        if (manyItHolds != null) {
            AskedAt holds = demands.get(manyItHolds);
            if (holds == null || holds.walking() == null) {
                return none("nothing says how many elements `" + container + "` holds");
            }
            size = holds.walking();
        }
        Optional<TermPath> across = counts.isEmpty() ? Optional.empty()
                : counts.getFirst().count().across();
        if (counts.stream().anyMatch(each -> !each.count().across().equals(across))) {
            return notChosen("the elements of `" + container + "` are counted in one container"
                    + " and across all of them, and are chosen for one of the two");
        }
        if (across.isPresent()) {
            return composeAcross(asked, standingAt, demands, container, across.get(), size,
                    together, sourceType, keptApart, apartAt, measuring, within, reading);
        }
        TypeView view = TypeView.of(sourceType, ruleSource.inners(), ruleSource.symbols(),
                ruleSource.kinds(), ruleSource.sums());
        if (!(view.shape() instanceof Shape.Sequence holding)
                || !container.element().outermostContainer().equals(container)) {
            return notChosen("`" + container + "` is no list or set written where it stands");
        }
        // A statement the elements meet together is one their values meet, which is what they are
        // chosen among their values for.
        List<AStatementAtARow> stated = new ArrayList<>();
        for (RealizationTarget.ElementsMeetingTogether each : together) {
            stated.add(AStatementAtARow.of(each.stated(), each.behavior(), measuring));
        }
        if (!stated.isEmpty()) {
            return amongItsValues(asked, stated, standingAt, demands, container, size, sourceType,
                    view, holding, keptApart, apartAt, measuring, within, reading,
                    new Standing.WhereItIsWritten(sourceType, reading));
        }
        // What another container is made to hold for the elements chooses none of their values,
        // so none are chosen apart that way.
        if (standingAt.isEmpty() && apartAt == null && counts.stream().allMatch(
                each -> ACountHandedOn.of(each.count()).isPresent())) {
            List<ACountHandedOn> handed = new ArrayList<>();
            List<OptionalInt> meeting = new ArrayList<>();
            for (RealizationTarget.ACount each : counts) {
                handed.add(ACountHandedOn.of(each.count()).orElseThrow());
                meeting.add(ACountHandedOn.counted(demands.get(each)));
            }
            return handingOn(asked, handed, meeting, size, view, keptApart, reading);
        }
        Element element = Element.of(counts, container);
        boolean inside = standingAt.stream()
                .anyMatch(each -> !each.term().subjectPath().equals(container.element()));
        // An element that is more than one number is chosen among the values it is read at
        // whole; and so is every element whose different values are counted, since what is
        // shared out then is the elements holding one value together, however many there are of
        // each.
        if (element == null || inside || apartAt != null) {
            return amongItsValues(asked, List.of(), standingAt, demands, container, size,
                    sourceType, view, holding, keptApart, apartAt, measuring, within, reading,
                    new Standing.WhereItIsWritten(sourceType, reading));
        }
        for (RealizationTarget.OfANumber each : standingAt) {
            AskedAt at = demands.get(each);
            if (at == null || at.walking() == null) {
                return none("nothing says where an element of `" + container + "` is to stand");
            }
            asked.add(new Asked.SomeElementIn(at.walking(), element.carrier()));
        }
        // The numbers beside an element, each at the one value the row was fixed at.
        Map<NumericTerm, Place> beside = new LinkedHashMap<>();
        Map<TermPath, ObservedValue> written = new LinkedHashMap<>();
        for (NumericTerm term : element.beside()) {
            Carrier on = element.on().get(term);
            Place at = settled(within, term);
            if (on == null || at == null) {
                return none("`" + term + "` stands at no one value beside the elements of `"
                        + container + "`");
            }
            beside.put(term, at);
            writtenAt(term, at, measuring, written);
        }
        NumericDomain.Bounds run = switch (within.projectionOf(element.term())) {
            case NumericDomain.FormProjection.Within(NumericDomain.Bounds held) ->
                    held == null ? NumericDomain.Bounds.OPEN : held;
            case NumericDomain.FormProjection.NothingIsLeft _ -> null;
            case null -> NumericDomain.Bounds.OPEN;
        };
        // The element is the one number chosen, so elements kept apart at any run of it — a set's,
        // or a list's its rules keep apart — are elements holding no number twice.
        boolean distinct = !ElementsKeptApart.at(view, keptApart, reading).isEmpty();
        int perPart = distinct ? MOST_ELEMENTS : 1;
        Set<CompositionCapacity> unheld = new LinkedHashSet<>();
        Set<CompositionRepertoire> unnamed = EnumSet.noneOf(CompositionRepertoire.class);
        TypeView ofTheElement = TypeView.of(holding.element(), ruleSource.inners(),
                ruleSource.symbols(), ruleSource.kinds(), ruleSource.sums());
        List<Place> candidates = List.of();
        if (element.carrier().counts()) {
            List<ExactRatio> turns = new ArrayList<>();
            for (Asked one : asked) {
                List<ExactRatio> where = one.turnsAt(element.term(), beside);
                if (where == null) {
                    return notChosen("where `" + one + "` turns over an element of `" + container
                            + "` could not be worked out");
                }
                turns.addAll(where);
            }
            if (run != null) {
                candidates = valuesAlong(element.carrier(), run, turns, perPart,
                        UsualPlaces.of(element.term(), element.carrier(), reading.today()),
                        unheld, unnamed);
            }
        } else {
            List<Place> turns = new ArrayList<>();
            for (Asked one : asked) {
                List<Place> where = one.placesTurnedAt(element.term(), beside);
                if (where == null) {
                    return notChosen("where `" + one + "` turns over an element of `" + container
                            + "` could not be worked out");
                }
                turns.addAll(where);
            }
            if (run != null) {
                candidates = valuesAlongAnOrder(element.carrier(), run, turns, perPart,
                        OfTheType.of(ofTheElement, reading), unnamed);
            }
        }
        Groups<Place> groups =
                Groups.of(asked, container, element, written, candidates).keptBy(asked);
        List<FixtureTemplate> built = new ArrayList<>();
        Set<CompositionBudget> refused = EnumSet.noneOf(CompositionBudget.class);
        Sharing sharing = new Sharing(groups, asked, List.of(), size,
                g -> distinct ? groups.values().get(g).size() : Integer.MAX_VALUE, MOST_SHARES);
        for (int elements = 0; ; elements++) {
            if (elements > MOST_ELEMENTS) {
                refused.add(CompositionBudget.ELEMENTS_A_COUNT_IS_COMPOSED_WITH);
                break;
            }
            // Each sharing is built as it is found, so what stops the walk is a container offered
            // or a sharing looked at, and never a list of them made first.
            boolean walkedThem = sharing.each(elements, share -> {
                if (built.size() == MOST_OFFERED) {
                    return false;
                }
                List<Place> values = groups.drawn(share, distinct);
                if (readsAsAsked(asked, container, element, written, values)) {
                    FixtureTemplate one = holdingThese(values, element.carrier(), view,
                            ofTheElement, ruleSource);
                    if (one != null) {
                        built.add(one);
                    }
                }
                return true;
            });
            // Stopped with a sharing in front of it: for the sharings this looks at, or else for the
            // containers it offers, which is the one other thing that turns a sharing away.
            if (!walkedThem) {
                refused.add(sharing.spent() ? CompositionBudget.SHARES_A_COUNT_IS_TRIED_AT
                        : CompositionBudget.CONTAINERS_A_COUNT_IS_OFFERED);
                break;
            }
        }
        if (!groups.unread().isEmpty()) {
            unnamed.add(CompositionRepertoire.ELEMENTS_CHOSEN_FOR_A_COUNT);
        }
        CompositionShortfall rest = CompositionShortfall.of(refused, unnamed, unheld);
        if (!built.isEmpty()) {
            return new TermRealizations.Realization.Built(built, rest);
        }
        if (!rest.figures().isEmpty()) {
            return new TermRealizations.Realization.Stopped(rest);
        }
        if (!rest.nothing()) {
            return new TermRealizations.Realization.Unexhausted(rest, groups.unreadSaid());
        }
        String alone = chosenAlone(asked, container, null);
        return alone != null ? notChosen(alone)
                : none("no container of `" + container + "` this composed meets every count asked");
    }

    /**
     * Containers inside the elements of the container at {@code across}, every element of all of
     * them together meeting the counts asked of their different values.
     *
     * <p>In two steps. The elements are chosen as one container of them would be
     * ({@link #amongItsValues}), which is every element there is, read as held by the one element
     * of the outer container ({@link ElementValues#asTheOneElementOf}): how many different values
     * the elements meeting a statement hold, and what the elements under one value come to, are
     * the same however they are shared out over the containers, so long as what each is asked
     * reads nothing of the element holding its container — which that one element, holding
     * nothing but the container, does not walk to. Then each choice is shared out over the
     * containers ({@link NestedContainersAddingUp#holdingThe}), the elements under one value
     * falling into different ones where the counts of the containers leave room.
     *
     * <p>Not where something is asked of how many elements one of the containers holds, nor of a
     * statement its elements meet together: either is a question about one container, and the
     * elements are chosen for all of them.
     */
    private static TermRealizations.Realization composeAcross(
            List<Asked> asked, List<RealizationTarget.OfANumber> standingAt,
            SequencedMap<RealizationTarget, AskedAt> demands, TermPath container, TermPath across,
            NumericSet size, List<RealizationTarget.ElementsMeetingTogether> together,
            Type sourceType, List<List<String>> keptApart, TermPath apartAt,
            Quantities measuring, SearchRegion within, RuleReadingContext reading) {
        if (size != null || !together.isEmpty()) {
            return notChosen("`" + container + "` is asked something of one of the containers,"
                    + " and its elements are chosen across all of them");
        }
        RuleReadingSource ruleSource = reading.source();
        NestedContainersAddingUp.Inside inner =
                NestedContainersAddingUp.ofTheContainerAt(sourceType, container, reading);
        if (inner == null || !across.equals(container.element().outermostContainer())) {
            return notChosen("`" + container + "` is no list or set inside the elements of a list"
                    + " or set written where it stands");
        }
        TypeView view = TypeView.of(inner.type(), ruleSource.inners(), ruleSource.symbols(),
                ruleSource.kinds(), ruleSource.sums());
        if (!(view.shape() instanceof Shape.Sequence holding)) {
            return notChosen("`" + container + "` is no list or set");
        }
        return amongItsValues(asked, List.of(), standingAt, demands, container, null,
                inner.type(), view, holding, inner.keptApart(), apartAt, measuring, within, reading,
                new Standing.AcrossTheElementsOf(across, container, sourceType, keptApart, within,
                        reading));
    }

    /**
     * Where the elements chosen for a container stand in the input: the row a container of them
     * is read as, and the rows written holding them.
     */
    private sealed interface Standing {

        /** {@code holding}, a row holding a container of the elements chosen, as it is read. */
        BorderQuantity.Observation read(BorderQuantity.Observation holding);

        /** The rows holding {@code values}, with what writing them met — or null where they are
         *  written as nothing. */
        TermRealizations.Realization written(List<ObservedValue> values);

        /** The container where it stands, of {@code type}. */
        record WhereItIsWritten(Type type, RuleReadingContext reading) implements Standing {

            @Override
            public BorderQuantity.Observation read(BorderQuantity.Observation holding) {
                return holding;
            }

            @Override
            public TermRealizations.Realization written(List<ObservedValue> values) {
                return ObservedFixtures.of(new ObservedValue.Sequence(values), type, reading)
                        instanceof ObservedFixtures.Writing.Written<FixtureTemplate>(
                                FixtureTemplate one)
                        ? new TermRealizations.Realization.Built(List.of(one),
                                CompositionShortfall.NONE)
                        : null;
            }
        }

        /**
         * The containers at {@code container} inside the elements of the one at {@code across},
         * of {@code type}, all of them put end to end: read as the one element of it holding them
         * all, and written shared out over them ({@link #composeAcross}).
         */
        record AcrossTheElementsOf(TermPath across, TermPath container, Type type,
                                   List<List<String>> keptApart, SearchRegion within,
                                   RuleReadingContext reading) implements Standing {

            @Override
            public BorderQuantity.Observation read(BorderQuantity.Observation holding) {
                return ElementValues.asTheOneElementOf(across, holding);
            }

            @Override
            public TermRealizations.Realization written(List<ObservedValue> values) {
                return new NestedContainersAddingUp(container.element()).holdingThe(type,
                        keptApart, values, within, reading);
            }
        }
    }

    /**
     * Containers counted only for statements that hold of other containers, with as many elements
     * meeting each as {@code meeting} says, and at every size that leaves room for them.
     *
     * <p>Which elements meet a statement is nothing the elements themselves turn on: each meets it
     * by what another container is made to hold for it, and that container is handed what makes the
     * first so many meet it and the rest not ({@link ACountHandedOn}). So a container of each size
     * from the most counted up is offered, holding whatever the element's own rules admit — no two
     * equal where some are counted and others not — and what it comes to beside is said as written
     * some of: which elements a row could hold instead is not walked here, so composing nothing is
     * no answer about the model.
     *
     * @param handed  what each count hands on, in the order of {@code asked}
     * @param meeting how many elements meet each count's statement, in the order of {@code asked}:
     *                what {@link ACountHandedOn#counted} says of the number each is asked at, and
     *                nothing where it says nothing
     * @param keptApart what the rules of the value holding the container keep its elements apart
     *                  at, which every container offered here keeps as well
     */
    private static TermRealizations.Realization handingOn(List<Asked> asked,
                                                          List<ACountHandedOn> handed,
                                                          List<OptionalInt> meeting,
                                                          NumericSet size, TypeView view,
                                                          List<List<String>> keptApart,
                                                          RuleReadingContext reading) {
        List<FixtureTemplate> built = new ArrayList<>();
        Set<CompositionBudget> refused = EnumSet.noneOf(CompositionBudget.class);
        CompositionShortfall met = CompositionShortfall.NONE;
        int least = 0;
        for (int i = 0; i < meeting.size(); i++) {
            // No count up to the most elements a container for one is composed with: the figure
            // stopped it, and is said.
            if (meeting.get(i).isEmpty()) {
                return new TermRealizations.Realization.Stopped(CompositionShortfall.of(
                        Set.of(CompositionBudget.ELEMENTS_A_COUNT_IS_COMPOSED_WITH),
                        Set.of(CompositionRepertoire.ELEMENTS_CHOSEN_FOR_A_COUNT), Set.of()));
            }
            if (!(asked.get(i) instanceof Asked.SoManyMeeting count)
                    || !count.asMany(meeting.get(i).getAsInt())) {
                return new TermRealizations.Realization.Unexhausted(CompositionShortfall.of(
                        Set.of(), Set.of(CompositionRepertoire.ELEMENTS_CHOSEN_FOR_A_COUNT),
                        Set.of()), "no count walked of what is counted is one a container"
                        + " composed with that many meeting it is asked for");
            }
            least = Math.max(least, meeting.get(i).getAsInt());
        }
        offering:
        for (int elements = least; ; elements++) {
            if (elements > MOST_ELEMENTS) {
                refused.add(CompositionBudget.ELEMENTS_A_COUNT_IS_COMPOSED_WITH);
                break;
            }
            if (size != null && !size.holds(Count.of(elements), Carrier.WHOLE)) {
                continue;
            }
            // Where some of the elements meet a statement and the rest do not, the other container
            // holds the value of each that does and none equal to that of each that does not, so
            // no two of them may be equal: a container of that many apart is what is asked for.
            // Elsewhere any container of that size is.
            // Apart at what each such statement's other container is asked about, which is what
            // tells the elements on its two sides apart.
            List<List<String>> splitAt = new ArrayList<>();
            boolean cannotSplit = false;
            for (int i = 0; i < meeting.size(); i++) {
                int counted = meeting.get(i).getAsInt();
                if (counted > 0 && counted < elements) {
                    List<String> fields = handed.get(i).fieldsToTheValue();
                    cannotSplit |= fields == null;
                    if (fields != null && !splitAt.contains(fields)) {
                        splitAt.add(fields);
                    }
                }
            }
            List<FixtureTemplate> ofThatSize = new ArrayList<>();
            if (cannotSplit) {
                continue;
            }
            // What building them met is carried on as what the offer was short of: a container
            // of that many whose elements' values were cut at a figure is one this did not build.
            Proposals made = !splitAt.isEmpty()
                    ? Witnesses.apart(view, elements, splitAt, keptApart, reading)
                    : Witnesses.ofSize(view, elements, keptApart, reading, Set.of());
            ofThatSize.addAll(made.values());
            met = met.and(made.met());
            for (FixtureTemplate bare : ofThatSize) {
                FixtureTemplate one = WornNames.under(view.wrappers(), bare, reading.source());
                if (one == null) {
                    continue;
                }
                // One more to offer than the figure lets through: what stopped it is said.
                if (built.size() == MOST_OFFERED) {
                    refused.add(CompositionBudget.CONTAINERS_A_COUNT_IS_OFFERED);
                    break offering;
                }
                built.add(one);
            }
        }
        CompositionShortfall rest = CompositionShortfall.of(refused,
                Set.of(CompositionRepertoire.ELEMENTS_CHOSEN_FOR_A_COUNT), Set.of()).and(met);
        if (!built.isEmpty()) {
            return new TermRealizations.Realization.Built(built, rest);
        }
        if (!rest.figures().isEmpty()) {
            return new TermRealizations.Realization.Stopped(rest);
        }
        return new TermRealizations.Realization.Unexhausted(rest, "no size of the container the"
                + " rules leave has room for as many elements as are counted");
    }

    /**
     * Containers meeting every count {@code asked}, with elements chosen among the values an
     * element is read at whole ({@link ValuesOfAnElement}): every value of each part that has only
     * so many, and at each number the values the statements part its run at.
     *
     * <p>Each value is read whole, the way a row holding a container of it alone is read, for every
     * statement at once; the values are grouped by what they answer and shared out among the counts
     * as numbers are ({@link Sharing}); and each container is read again whole before it is offered.
     * Read the way a row is, a value answers here what it answers in a row — so elements meeting
     * the statements different ways, which no element written alike does, are a container this
     * offers.
     *
     * <p>Where some part of the element is one nothing here chooses values of, or the counts ask
     * something beside the elements' statements, the container is no container chosen this way
     * and is said to be that.
     *
     * <p><b>And statements the elements meet together, one of several ways.</b> What such a
     * statement says of each element — what some element meets, how many meet something — is one
     * more thing each value answers and the values are grouped by, with no count of it asked. A
     * sharing is turned away as soon as how many elements of it may meet each of those leaves the
     * statement no way of holding ({@link AStatementAtARow#counting}), so which of its ways the
     * container takes is the sharing's and none is taken first; and a container is offered only
     * where the statement holds of it, read with some element of it standing where the row reads
     * one.
     *
     * @param counted    what the counts ask, one for each
     * @param together   statements the elements meet together, each about {@code container} alone
     * @param standingAt numbers inside an element, each asked to stand in a set: a value the row
     *                   places there, which some element of the container holds
     * @param holding    what the container is, a list or a set
     * @param standing   where the elements chosen stand in the input: how a container of them is
     *                   read, and the rows written holding them
     */
    private static TermRealizations.Realization amongItsValues(List<Asked> counted,
                                                               List<AStatementAtARow> together,
                                                               List<RealizationTarget.OfANumber>
                                                                       standingAt,
                                                               SequencedMap<RealizationTarget,
                                                                       AskedAt> demands,
                                                               TermPath container,
                                                               NumericSet size, Type sourceType,
                                                               TypeView view,
                                                               Shape.Sequence holding,
                                                               List<List<String>> keptApart,
                                                               TermPath apartAt,
                                                               Quantities measuring,
                                                               SearchRegion within,
                                                               RuleReadingContext reading,
                                                               Standing standing) {
        List<Asked> asked = new ArrayList<>(counted);
        for (RealizationTarget.OfANumber each : standingAt) {
            AskedAt at = demands.get(each);
            TermOrders orders = measuring.ordersOf(each.term());
            Carrier on = orders == null ? null : orders.observed();
            if (at == null || at.walking() == null || on == null) {
                return none("nothing says where `" + each.term() + "` is to stand inside an"
                        + " element of `" + container + "`");
            }
            asked.add(new Asked.SomeElementAt(each.term().subjectPath(), at.walking(), on));
        }
        // What each statement of the elements together says of one element, once however many of
        // them say it, with no count of it asked: where in what is asked each is.
        List<Together> statements = new ArrayList<>();
        Map<String, Integer> saidOfAnElement = new LinkedHashMap<>();
        for (AStatementAtARow each : together) {
            Map<String, Integer> at = new LinkedHashMap<>();
            each.ofEachElementOf(container).forEach((key, perElement) -> {
                Integer index = saidOfAnElement.get(key);
                if (index == null) {
                    index = asked.size();
                    asked.add(new Asked.SoManyMeeting(perElement, ANY_COUNT, Optional.empty()));
                    saidOfAnElement.put(key, index);
                }
                at.put(key, index);
            });
            statements.add(new Together(each.counting(container, at, MOST_ELEMENTS)));
        }
        // What an element read whole answers of each, which is what the element is chosen by.
        List<Function<BorderQuantity.Observation, AStatementAtARow.Answer>> ofAnElement =
                new ArrayList<>();
        for (Asked each : asked) {
            ofAnElement.add(switch (each) {
                case Asked.SoManyMeeting many -> many.perElement()::at;
                case Asked.SomeElementAt some -> some::ofAnElement;
                case Asked.SomeElementIn _ -> throw new IllegalStateException(
                        "an element standing in a set is one number, and is chosen as one");
            });
        }
        // Elements its rules keep apart are chosen among more than one value of each part.
        List<List<String>> apartByItsRules = ElementsKeptApart.at(view, keptApart, reading);
        boolean keptApartByItsRules = !apartByItsRules.isEmpty();
        Set<CompositionCapacity> unheld = new LinkedHashSet<>();
        Set<CompositionRepertoire> unnamed = EnumSet.noneOf(CompositionRepertoire.class);
        // The numbers the statements read beside an element, each at the one value the row was
        // fixed at, which the row an element is read in holds too.
        Map<TermPath, ObservedValue> written = new LinkedHashMap<>();
        Map<NumericTerm, Place> beside = settledOutside(asked, measuring, within, written);
        // Where the different values at a place are counted, the values that place is chosen at
        // are as many as a container has elements, and the elements are listed holding one of
        // them there at a time: which value a group is under is apart from what it holds
        // ({@link UnderEachValue}), and listed against every value of the other parts, those
        // values would fill the listing in place of the others'.
        BiFunction<TermPath, TypeView, List<ObservedValue>> numbers = (at, part) ->
                numbersAt(at, OfTheType.of(part, reading), asked, apartAt, measuring, within,
                        beside, keptApartByItsRules ? MOST_ELEMENTS : 1, unheld, unnamed,
                        reading.today());
        ListedByValue byValue = listedByValue(container, holding.element(), reading, apartAt,
                numbers, (at, part) -> numbersAt(at, OfTheType.manyOf(part, reading), asked,
                        apartAt, measuring, within, beside, MOST_ELEMENTS, unheld, unnamed,
                        reading.today()));
        if (byValue == null) {
            return notChosen("an element of `" + container + "` has a part whose values are"
                    + " neither one of so many nor numbers the statements part");
        }
        if (apartAt != null && byValue.values().isEmpty()) {
            return notChosen("the different values at `" + apartAt + "` are counted, and no"
                    + " value is chosen there as a part of an element of `" + container + "`");
        }
        ElementValues ofTheElement = byValue.first();
        ValuesOfAnElement.Listed listed = ofTheElement.listed();
        List<FixtureTemplate> built = new ArrayList<>();
        Set<CompositionBudget> refused = EnumSet.noneOf(CompositionBudget.class);
        if (!listed.all()) {
            refused.add(CompositionBudget.VALUES_AN_ELEMENT_IS_CHOSEN_AMONG);
        }
        Function<List<ObservedValue>, BorderQuantity.Observation> holdingThem =
                values -> standing.read(withNumbersBeside(ofTheElement.holding(sourceType, values),
                        written));
        // Where the different values at a place are counted, what is shared out is the elements
        // holding one value there together, each group with a value of its own: how many values
        // a count has is how many such groups it has, whatever each holds. Elsewhere, each
        // element on its own.
        Groups<?> groups;
        IntUnaryOperator capacity;
        Function<int[], List<ObservedValue>> drawing;
        if (apartAt == null) {
            Groups<ObservedValue> every = Groups.none();
            for (ObservedValue value : listed.values()) {
                BorderQuantity.Observation row = holdingThem.apply(List.of(value));
                every.add(value, i -> ofAnElement.get(i).apply(row), asked.size());
            }
            Groups<ObservedValue> kept = every.keptBy(asked);
            groups = kept;
            capacity = g -> keptApartByItsRules ? kept.values().get(g).size() : Integer.MAX_VALUE;
            drawing = share -> kept.drawn(share, keptApartByItsRules);
        } else {
            UnderEachValue under = UnderEachValue.of(byValue.values().size(), byValue.under(),
                    holdingThem, container, apartAt, asked, keptApartByItsRules,
                    UnderEachValue.oneEachUnder(container, apartAt, apartByItsRules), refused);
            groups = under.groups();
            capacity = under::capacity;
            drawing = under::drawn;
        }
        Sharing sharing = new Sharing(groups, asked, statements, size, capacity, MOST_SHARES);
        for (int elements = 0; ; elements++) {
            if (elements > MOST_ELEMENTS) {
                refused.add(CompositionBudget.ELEMENTS_A_COUNT_IS_COMPOSED_WITH);
                break;
            }
            boolean walkedThem = sharing.each(elements, share -> {
                // At or past it: one choice of the elements may be written as several rows.
                if (built.size() >= MOST_OFFERED) {
                    return false;
                }
                List<ObservedValue> values = drawing.apply(share);
                if (values == null) {
                    return true;
                }
                BorderQuantity.Observation whole = holdingThem.apply(values);
                for (Asked each : asked) {
                    // A count reads the container through the row and not the values handed it.
                    if (!(each.over(container, List.of(), whole)
                            instanceof AStatementAtARow.Answer.Holds)) {
                        return true;
                    }
                }
                if (!sharing.holdsTogether() && !heldTogether(together, container, whole)) {
                    return true;
                }
                TermRealizations.Realization rows = standing.written(values);
                if (rows == null) {
                    return true;
                }
                if (rows instanceof TermRealizations.Realization.Built made) {
                    made.values().forEach(built::add);
                }
                CompositionShortfall met = rows.shortfall();
                refused.addAll(met.figures());
                unnamed.addAll(met.populations());
                unheld.addAll(met.unheld());
                return true;
            });
            if (!walkedThem) {
                refused.add(sharing.spent() ? CompositionBudget.SHARES_A_COUNT_IS_TRIED_AT
                        : CompositionBudget.CONTAINERS_A_COUNT_IS_OFFERED);
                break;
            }
        }
        if (!groups.unread().isEmpty()) {
            unnamed.add(CompositionRepertoire.ELEMENTS_CHOSEN_FOR_A_COUNT);
        }
        CompositionShortfall rest = CompositionShortfall.of(refused, unnamed, unheld);
        if (!built.isEmpty()) {
            return new TermRealizations.Realization.Built(built, rest);
        }
        if (!rest.figures().isEmpty()) {
            return new TermRealizations.Realization.Stopped(rest);
        }
        if (!rest.nothing()) {
            return new TermRealizations.Realization.Unexhausted(rest, groups.unreadSaid());
        }
        String alone = chosenAlone(asked, container, apartAt);
        return alone != null ? notChosen(alone)
                : none("no container of `" + container + "` this composed meets every count asked");
    }

    /**
     * Why finding no container of {@code container} for {@code asked} shows none, or null where it
     * does. The elements are chosen by what a row holding a group of them alone answers — the
     * elements under one value at {@code under}, or one element where it is null — and that is
     * what the group comes to in any container only where an element's answer turns on nothing
     * beyond its group and not on the order its elements are handed in
     * ({@link AStatementAtARow.TurnsOn}). Elsewhere a container chosen that way is still read
     * whole before it is offered, so what is offered holds; what is not found is not shown absent.
     */
    private static String chosenAlone(List<Asked> asked, TermPath container, TermPath under) {
        AStatementAtARow.TurnsOn turns = AStatementAtARow.TurnsOn.THE_ELEMENT;
        for (Asked each : asked) {
            turns = turns.orMore(each.turnsOnAmong(container, under));
        }
        return switch (turns) {
            case THE_ELEMENT, THOSE_UNDER_ITS_VALUE -> null;
            case THE_ORDER_OF_THOSE_UNDER_ITS_VALUE -> "what an element of `" + container
                    + "` answers turns on which of the elements holding its value at `" + under
                    + "` is handed last, and a group of them is chosen by which elements it holds";
            case OTHER_ELEMENTS -> "what an element of `" + container + "` answers turns on"
                    + (under == null ? " the elements beside it, and each is chosen by what it"
                            + " answers alone" : " elements not holding its value at `" + under
                            + "`, and the elements holding one value are chosen by what they"
                            + " answer alone");
        };
    }

    /**
     * A statement the elements of a container meet together, read as what it comes to from how
     * many of them meet each thing it says of one element — each where it is in what the elements
     * are asked.
     */
    private record Together(AStatementAtARow.Counting counting) {}

    /**
     * Whether every one of {@code together} holds of the container {@code row} holds, read with
     * one element of it standing where a row reads one — the same element for all of them, since
     * what they say of the element a row stands at is said of one element. A container holding
     * none is read as it stands.
     */
    private static boolean heldTogether(List<AStatementAtARow> together, TermPath container,
                                        BorderQuantity.Observation row) {
        if (together.isEmpty()) {
            return true;
        }
        if (!(row.eachElementOf(container) instanceof WalkResult.Reached<
                List<BorderQuantity.Observation>>(var elements))) {
            return false;
        }
        for (BorderQuantity.Observation standing : elements.isEmpty() ? List.of(row) : elements) {
            if (together.stream().allMatch(each ->
                    each.at(standing) instanceof AStatementAtARow.Answer.Holds)) {
                return true;
            }
        }
        return false;
    }

    /**
     * The numbers {@code asked} reads whose turns are turns of {@code term}, a number of an
     * element, where the elements are grouped under the value at {@code apartAt}.
     *
     * @param asItself the number itself, and an end of it gathered under that value, of every
     *                 element: the end of a group is one of its elements' numbers, so it turns
     *                 where an element's does
     * @param addedUp  a total of it gathered under that value, of every element: a group of so
     *                 many elements comes to a total at a place where its elements stand at about
     *                 that place shared among them
     */
    private record TurningWith(List<NumericTerm> asItself, List<NumericTerm> addedUp) {}

    private static TurningWith turningWith(NumericTerm term, TermPath apartAt,
                                           List<Asked> asked) {
        List<NumericTerm> asItself = new ArrayList<>(List.of(term));
        List<NumericTerm> addedUp = new ArrayList<>();
        if (apartAt == null) {
            return new TurningWith(asItself, addedUp);
        }
        for (Asked one : asked) {
            if (!(one instanceof Asked.SoManyMeeting(AStatementAtARow perElement, _, _))) {
                continue;
            }
            for (NumericTerm number : perElement.numbers()) {
                if (number instanceof NumericTerm.GatheredUnderItsKey gathered
                        && gathered.selection() == null
                        && gathered.key() instanceof ElementKey.At(ElementProjection way)
                        && way.from(gathered.elements()).equals(apartAt)
                        && gathered.value().asAPlace() instanceof ElementProjection place
                        && place.from(gathered.elements()).equals(term.subjectPath())) {
                    List<NumericTerm> into = switch (gathered.gathering()) {
                        case NumericTerm.GatheredUnderItsKey.Gathering.End _ -> asItself;
                        case NumericTerm.GatheredUnderItsKey.Gathering.Total _ -> addedUp;
                        case NumericTerm.GatheredUnderItsKey.Gathering.SinceAPut _ -> null;
                    };
                    if (into != null && !into.contains(number)) {
                        into.add(number);
                    }
                }
            }
        }
        return new TurningWith(asItself, addedUp);
    }

    /**
     * The values of the number at {@code at} inside an element that are read for {@code asked}:
     * each place a statement turns over at, and {@code each} values of every run between them,
     * inside what the rules leave it and values of {@code part} — or null where the number is on
     * no order, or where a statement turns over at it could not be worked out.
     *
     * <p>Where the different values at {@code apartAt} are counted, an end of the number at
     * {@code at} gathered under the value there turns where the number does, and a total of it
     * turns, over a group of so many elements, where the number stands at that share of the place
     * ({@link #turningWith}): those shares are where an element is chosen too.
     */
    private static List<ObservedValue> numbersAt(TermPath at, OfTheType part, List<Asked> asked,
                                                 TermPath apartAt, Quantities measuring,
                                                 SearchRegion within,
                                                 Map<NumericTerm, Place> beside, int each, Set<CompositionCapacity> unheld,
                                                 Set<CompositionRepertoire> unnamed, Today today) {
        NumericTerm term = new NumericTerm.ValueOf(at);
        TermOrders orders = measuring.ordersOf(term);
        Carrier carrier = orders == null ? null : orders.observed();
        if (carrier == null) {
            return null;
        }
        NumericDomain.Bounds run = switch (within.projectionOf(term)) {
            case NumericDomain.FormProjection.Within(NumericDomain.Bounds held) ->
                    held == null ? NumericDomain.Bounds.OPEN : held;
            case NumericDomain.FormProjection.NothingIsLeft _ -> null;
            case null -> NumericDomain.Bounds.OPEN;
        };
        if (run == null) {
            return List.of();
        }
        TurningWith turning = turningWith(term, apartAt, asked);
        List<Place> places;
        if (carrier.counts()) {
            List<ExactRatio> turns = new ArrayList<>();
            for (Asked one : asked) {
                for (NumericTerm number : turning.asItself()) {
                    List<ExactRatio> where = one.turnsAt(number, beside);
                    if (where == null) {
                        return null;
                    }
                    turns.addAll(where);
                }
                for (NumericTerm number : turning.addedUp()) {
                    List<ExactRatio> where = one.turnsAt(number, beside);
                    if (where == null) {
                        return null;
                    }
                    for (ExactRatio total : where) {
                        for (int shared = 1; shared <= MOST_ELEMENTS; shared++) {
                            if (total.dividedBy(ExactRatio.of(shared))
                                    instanceof ExactAnswer.Held<ExactRatio>(ExactRatio share)) {
                                turns.add(share);
                            }
                        }
                    }
                }
            }
            places = valuesAlong(carrier, run, turns, each,
                    UsualPlaces.of(term, carrier, today), unheld, unnamed);
        } else {
            List<Place> turns = new ArrayList<>();
            for (Asked one : asked) {
                for (NumericTerm number : turning.asItself()) {
                    List<Place> where = one.placesTurnedAt(number, beside);
                    if (where == null) {
                        return null;
                    }
                    turns.addAll(where);
                }
            }
            places = valuesAlongAnOrder(carrier, run, turns, each, part, unnamed);
        }
        List<ObservedValue> out = new ArrayList<>();
        for (Place place : places) {
            out.add(carrier.valueOf(place));
        }
        return out;
    }

    /**
     * Containers of {@code sourceType} holding some element as often as {@code alike} asks, and as
     * many elements as {@code manyItHolds} asks where it is not null.
     *
     * <p>Which value it is that occurs is no part of what is asked: any one value occurring that
     * often answers it, so one is taken from the values the element's own number leaves and the
     * container is that value as many times as asked, with other values beside it where the size
     * asked for is larger. The elements are those values and nothing else is chosen for them, so
     * the key is the element itself.
     */
    static TermRealizations.Realization composeAlike(Type sourceType,
                                                     List<List<String>> keptApart,
                                                     RealizationTarget.OfANumber alike,
                                                     RealizationTarget.OfANumber manyItHolds,
                                                     SequencedMap<RealizationTarget, AskedAt> demands,
                                                     Quantities measuring, SearchRegion within,
                                                     RuleReadingContext reading) {
        // Among the elements of one container, which is a count of the elements alike at a place;
        // or among those of them a statement keeps, which is the same count with the statement
        // put to every value chosen.
        TermPath place;
        KeptOccurrences kept = null;
        switch (alike.term()) {
            case NumericTerm.Multiplicity among -> place = among.place();
            case NumericTerm.OccurrencesOfItsValue among -> {
                place = among.subjectPath();
                kept = among.selection();
            }
            default -> throw new IllegalStateException(alike.term() + " is no count of how often"
                    + " an element's value occurs");
        }
        TermPath container = alike.term() instanceof NumericTerm.Multiplicity among
                ? among.container() : place.containersHoldingIt().getFirst();
        RuleReadingSource ruleSource = reading.source();
        AskedAt asked = demands.get(alike);
        if (asked == null || asked.walking() == null) {
            return none("nothing says how often an element of `" + container + "` is to occur");
        }
        NumericSet wanted = asked.walking();
        NumericSet size = null;
        if (manyItHolds != null) {
            AskedAt holds = demands.get(manyItHolds);
            if (holds == null || holds.walking() == null) {
                return none("nothing says how many elements `" + container + "` holds");
            }
            size = holds.walking();
        }
        TypeView view = TypeView.of(sourceType, ruleSource.inners(), ruleSource.symbols(),
                ruleSource.kinds(), ruleSource.sums());
        if (!(view.shape() instanceof Shape.Sequence holding)
                || !container.element().outermostContainer().equals(container)) {
            return notChosen("`" + container + "` is no list or set written where it stands, to"
                    + " hold an element as often as asked (it stands as " + sourceType + ")");
        }
        // Alike at a place inside the element, the elements holding one value there are chosen
        // together, as many as asked, among the values each is read at whole.
        if (!place.equals(container.element())) {
            return alikeUnderOneValue(sourceType, view, holding, container, place, kept, wanted,
                    size, keptApart, measuring, within, reading);
        }
        NumericTerm own = new NumericTerm.ValueOf(container.element());
        TermOrders orders = measuring.ordersOf(own);
        Carrier carrier = orders == null ? null : orders.observed();
        if (carrier == null) {
            return notChosen("an element of `" + container + "` is on no order its values are"
                    + " chosen on");
        }
        NumericDomain.Bounds run = switch (within == null ? null : within.projectionOf(own)) {
            case NumericDomain.FormProjection.Within(NumericDomain.Bounds held) ->
                    held == null ? NumericDomain.Bounds.OPEN : held;
            case NumericDomain.FormProjection.NothingIsLeft _ -> null;
            case null -> NumericDomain.Bounds.OPEN;
        };
        if (run == null) {
            return none("the rules leave no value for an element of `" + container + "`");
        }
        // One value to repeat and as many different ones beside it as the size asked for leaves
        // room for; elements kept apart — a set's, or a list's its rules keep apart — hold each
        // value once, so they hold nothing repeated. The element is the number, so apart at any run
        // of it is apart as numbers.
        boolean distinct = !ElementsKeptApart.at(view, keptApart, reading).isEmpty();
        Set<CompositionCapacity> unheld = new LinkedHashSet<>();
        Set<CompositionRepertoire> unnamed = EnumSet.noneOf(CompositionRepertoire.class);
        TypeView ofTheElement = TypeView.of(holding.element(), ruleSource.inners(),
                ruleSource.symbols(), ruleSource.kinds(), ruleSource.sums());
        // As many values as a container may hold different ones: a plain string order names
        // only the empty string.
        OfTheType repeated = OfTheType.manyOf(ofTheElement, reading);
        List<Place> candidates = valuesToCount(kept, own, container, place, carrier, run,
                repeated, unheld, unnamed, reading.today());
        if (candidates == null) {
            return notChosen("where `" + kept.key() + "` turns over an element of `"
                    + container + "` could not be worked out");
        }
        List<Place> beside = candidates.isEmpty() ? List.of()
                : valuesBeside(candidates.getFirst(), candidates, kept, carrier, run, repeated,
                        unheld, unnamed, reading.today());
        List<FixtureTemplate> built = new ArrayList<>();
        Set<CompositionBudget> refused = EnumSet.noneOf(CompositionBudget.class);
        for (int often = 1; often <= MOST_ELEMENTS && built.size() < MOST_OFFERED; often++) {
            if (!wanted.holds(Count.of(often), Carrier.WHOLE) || (distinct && often > 1)
                    || candidates.isEmpty()) {
                continue;
            }
            for (int total = often; total <= MOST_ELEMENTS && built.size() < MOST_OFFERED;
                    total++) {
                if (size != null && !size.holds(Count.of(total), Carrier.WHOLE)) {
                    continue;
                }
                if (total - often > beside.size()) {
                    break;
                }
                List<Place> values = new ArrayList<>();
                for (int i = 0; i < often; i++) {
                    values.add(candidates.getFirst());
                }
                values.addAll(beside.subList(0, total - often));
                FixtureTemplate one = occursAsOften(values, wanted)
                        ? holdingThese(values, carrier, view, ofTheElement, ruleSource) : null;
                if (one != null) {
                    built.add(one);
                }
                // The smallest container that is that many repeated is the one a row is written
                // with, so a larger one is offered only where a size was asked for.
                if (size == null) {
                    break;
                }
            }
        }
        // Containers holding an element more often than a container is composed with are not
        // looked at, which is the figure a reader raises where that is what the asked-for counts
        // run to.
        Endpoint mostOften = wanted.extent().max();
        if (mostOften == null || mostOften.at().compareTo(Count.of(MOST_ELEMENTS)) > 0) {
            refused.add(CompositionBudget.ELEMENTS_A_COUNT_IS_COMPOSED_WITH);
        }
        CompositionShortfall rest = CompositionShortfall.of(refused, unnamed, unheld);
        if (!built.isEmpty()) {
            return new TermRealizations.Realization.Built(built, rest);
        }
        if (!rest.figures().isEmpty()) {
            return new TermRealizations.Realization.Stopped(rest);
        }
        if (!rest.nothing()) {
            return new TermRealizations.Realization.Unexhausted(rest, null);
        }
        return none("no container of `" + container + "` this composed holds an element as often"
                + " as asked");
    }

    /**
     * Containers holding, at {@code place} inside their elements, some value as often as
     * {@code wanted} asks among the elements {@code kept} keeps — every element where it is null —
     * and as many elements as {@code size} asks where it is not null.
     *
     * <p>The elements holding that value are one group chosen among the groups of elements under
     * one value ({@link HeldUnder}), with as many as asked of them kept; the rest are each the one
     * element under a value of its own, so none of them is held as often unless it is asked to
     * be. The container is the parameter, its elements chosen among the values each is read at
     * whole.
     */
    private static TermRealizations.Realization alikeUnderOneValue(
            Type sourceType, TypeView view, Shape.Sequence holding, TermPath container,
            TermPath place, KeptOccurrences kept, NumericSet wanted, NumericSet size,
            List<List<String>> keptApart, Quantities measuring, SearchRegion within,
            RuleReadingContext reading) {
        List<Asked> asked = kept == null ? List.of()
                : List.of(new Asked.SoManyMeeting(kept.perElement(), ANY_COUNT, Optional.empty()));
        Set<CompositionCapacity> unheld = new LinkedHashSet<>();
        Set<CompositionRepertoire> unnamed = EnumSet.noneOf(CompositionRepertoire.class);
        Map<TermPath, ObservedValue> written = new LinkedHashMap<>();
        Map<NumericTerm, Place> beside = settledOutside(asked, measuring, within, written);
        List<List<String>> apart = ElementsKeptApart.at(view, keptApart, reading);
        ListedByValue byValue = listedByValue(container, holding.element(), reading, place,
                (at, part) -> numbersAt(at, OfTheType.of(part, reading), asked, null, measuring,
                        within, beside, apart.isEmpty() ? 1 : MOST_ELEMENTS, unheld, unnamed,
                        reading.today()),
                (at, part) -> numbersAt(at, OfTheType.manyOf(part, reading), asked, null,
                        measuring, within, beside, MOST_ELEMENTS, unheld, unnamed,
                        reading.today()));
        if (byValue == null) {
            return notChosen("an element of `" + container + "` has a part whose values are"
                    + " neither one of so many nor numbers the statements part");
        }
        if (byValue.values().isEmpty()) {
            return notChosen("an element of `" + container + "` is alike another at `" + place
                    + "`, and no value is chosen there as a part of the element");
        }
        ElementValues ofTheElement = byValue.first();
        Set<CompositionBudget> refused = EnumSet.noneOf(CompositionBudget.class);
        if (!ofTheElement.listed().all()) {
            refused.add(CompositionBudget.VALUES_AN_ELEMENT_IS_CHOSEN_AMONG);
        }
        UnderEachValue under = UnderEachValue.of(byValue.values().size(), byValue.under(),
                values -> withNumbersBeside(ofTheElement.holding(sourceType, values), written),
                container, place, asked, !apart.isEmpty(),
                UnderEachValue.oneEachUnder(container, place, apart), refused);
        Groups<HeldUnder> groups = under.groups();
        List<FixtureTemplate> built = new ArrayList<>();
        for (int often = 1; often <= MOST_ELEMENTS && built.size() < MOST_OFFERED; often++) {
            if (!wanted.holds(Count.of(often), Carrier.WHOLE)) {
                continue;
            }
            for (int total = often; total <= MOST_ELEMENTS && built.size() < MOST_OFFERED;
                    total++) {
                if (size != null && !size.holds(Count.of(total), Carrier.WHOLE)) {
                    continue;
                }
                // The groups are listed smallest first, and any of them may be the one under the
                // value: one holding more elements than are kept is one a container of this size
                // may take where one holding no more cannot.
                FixtureTemplate one = null;
                for (int asOften = 0; asOften < groups.weights().size() && one == null;
                        asOften++) {
                    one = asOftenUnderOneValue(groups, under, asOften, often, total,
                            kept != null, sourceType, reading);
                }
                if (one != null) {
                    built.add(one);
                }
                // The smallest container that is that many alike is the one a row is written with,
                // so a larger one is offered only where a size was asked for.
                if (size == null && one != null) {
                    break;
                }
            }
        }
        Endpoint mostOften = wanted.extent().max();
        if (mostOften == null || mostOften.at().compareTo(Count.of(MOST_ELEMENTS)) > 0) {
            refused.add(CompositionBudget.ELEMENTS_A_COUNT_IS_COMPOSED_WITH);
        }
        if (!groups.unread().isEmpty()) {
            unnamed.add(CompositionRepertoire.ELEMENTS_CHOSEN_FOR_A_COUNT);
        }
        CompositionShortfall rest = CompositionShortfall.of(refused, unnamed, unheld);
        if (!built.isEmpty()) {
            return new TermRealizations.Realization.Built(built, rest);
        }
        if (!rest.figures().isEmpty()) {
            return new TermRealizations.Realization.Stopped(rest);
        }
        if (!rest.nothing()) {
            return new TermRealizations.Realization.Unexhausted(rest, groups.unreadSaid());
        }
        String alone = chosenAlone(asked, container, place);
        return alone != null ? notChosen(alone)
                : none("no container of `" + container + "` this composed holds a value at `"
                        + place + "` as often as asked");
    }

    /**
     * A container of {@code total} elements whose {@code asOften}-th group comes to a value
     * occurring {@code often} times, or null where that group does not or no container is that.
     *
     * <p>How often a value occurs is of the elements under it a statement keeps, where
     * {@code kept}, and of every one of them otherwise: a group may hold elements the statement
     * does not keep beside those it does, and is as many elements as it holds whichever. The rest
     * of the container is groups of one element, each under a value of its own.
     */
    private static FixtureTemplate asOftenUnderOneValue(Groups<HeldUnder> groups,
                                                        UnderEachValue under, int asOften,
                                                        int often, int total, boolean kept,
                                                        Type sourceType,
                                                        RuleReadingContext reading) {
        int holds = groups.weights().get(asOften);
        if ((kept ? groups.counts().get(asOften)[0] : holds) != often || holds > total) {
            return null;
        }
        int[] share = new int[groups.weights().size()];
        share[asOften] = 1;
        int left = total - holds;
        for (int g = 0; g < share.length && left > 0; g++) {
            if (groups.weights().get(g) == 1) {
                int more = Math.min(left, under.capacity(g) - share[g]);
                share[g] += more;
                left -= more;
            }
        }
        List<ObservedValue> values = left > 0 ? null : under.drawn(share);
        return values != null && ObservedFixtures.of(new ObservedValue.Sequence(values),
                sourceType, reading) instanceof ObservedFixtures.Writing.Written<FixtureTemplate>(
                        FixtureTemplate one) ? one : null;
    }

    /**
     * Containers inside the elements of another holding some value as often as asked, in all of
     * them put end to end.
     *
     * <p>Which value it is that occurs is no part of what is asked: any one occurring that often
     * answers it, so one is taken from the values the place leaves and written as many times as
     * asked, spread over the containers, with other values beside it where the containers need
     * more leaves than the repeated value gives them ({@link NestedContainersAddingUp#alike}).
     * The values are the elements themselves: a place inside an element is a second thing the
     * elements are chosen at.
     */
    static TermRealizations.Realization composeAcrossContainers(
            Type sourceType, List<List<String>> keptApart, RealizationTarget.OfANumber alike,
            SequencedMap<RealizationTarget, AskedAt> demands, Quantities measuring,
            SearchRegion within, RuleReadingContext reading) {
        NumericTerm.OccurrencesOfItsValue term = (NumericTerm.OccurrencesOfItsValue) alike.term();
        TermPath place = term.subjectPath();
        AskedAt asked = demands.get(alike);
        if (asked == null || asked.walking() == null) {
            return none("nothing says how often a value at `" + place + "` is to occur");
        }
        NumericSet wanted = asked.walking();
        List<TermPath> chain = place.containersHoldingIt();
        if (chain.size() < 2 || !place.equals(chain.getLast().element())) {
            return notChosen("a value at `" + place + "` is not an element of the container it"
                    + " stands inside, so the elements are chosen at a place inside them");
        }
        NumericTerm own = new NumericTerm.ValueOf(place);
        TermOrders orders = measuring.ordersOf(own);
        Carrier carrier = orders == null ? null : orders.observed();
        if (carrier == null) {
            return notChosen("a value at `" + place + "` is on no order its values are chosen on");
        }
        NumericDomain.Bounds run = switch (within == null ? null : within.projectionOf(own)) {
            case NumericDomain.FormProjection.Within(NumericDomain.Bounds held) ->
                    held == null ? NumericDomain.Bounds.OPEN : held;
            case NumericDomain.FormProjection.NothingIsLeft _ -> null;
            case null -> NumericDomain.Bounds.OPEN;
        };
        if (run == null) {
            return none("the rules leave no value at `" + place + "`");
        }
        Set<CompositionCapacity> unheld = new LinkedHashSet<>();
        Set<CompositionRepertoire> unnamed = EnumSet.noneOf(CompositionRepertoire.class);
        KeptOccurrences kept = term.selection();
        OfTheType leaves = OfTheType.of(
                NestedContainersAddingUp.ofTheLeaves(sourceType, place, reading), reading);
        List<Place> candidates = valuesToCount(kept, own, chain.getLast(), place, carrier, run,
                leaves, unheld, unnamed, reading.today());
        if (candidates == null) {
            return notChosen("where `" + kept.key() + "` turns over an element of `"
                    + chain.getLast() + "` could not be worked out");
        }
        if (candidates.isEmpty()) {
            return none(kept == null ? "the rules leave no value at `" + place + "` to repeat"
                    : "no value at `" + place + "` to repeat that `" + kept.key() + "` keeps");
        }
        List<Place> beside = valuesBeside(candidates.getFirst(), candidates, kept, carrier, run,
                leaves, unheld, unnamed, reading.today());
        NestedContainersAddingUp nested = new NestedContainersAddingUp(place);
        List<FixtureTemplate> built = new ArrayList<>();
        CompositionShortfall rest = CompositionShortfall.NONE;
        UnbuiltAttempts unbuilt = new UnbuiltAttempts();
        for (int often = 1; often <= MOST_ELEMENTS && built.size() < MOST_OFFERED; often++) {
            if (!wanted.holds(Count.of(often), Carrier.WHOLE)) {
                continue;
            }
            // The fewest leaves that give each container the room its count asks, and no more of
            // them than another value is left for.
            for (int extra = 0; extra <= beside.size() && often + extra <= MOST_ELEMENTS;
                    extra++) {
                TermRealizations.Realization one = nested.alike(sourceType, keptApart,
                        List.of(new NestedContainersAddingUp.Counted(candidates.getFirst(),
                                often)),
                        beside.subList(0, extra), carrier, within, reading);
                if (one instanceof TermRealizations.Realization.Built made) {
                    built.addAll(made.values());
                    rest = rest.and(made.rest());
                    break;
                }
                unbuilt.add(one);
            }
        }
        Endpoint mostOften = wanted.extent().max();
        Set<CompositionBudget> refused = EnumSet.noneOf(CompositionBudget.class);
        if (mostOften == null || mostOften.at().compareTo(Count.of(MOST_ELEMENTS)) > 0) {
            refused.add(CompositionBudget.ELEMENTS_A_COUNT_IS_COMPOSED_WITH);
        }
        rest = rest.and(CompositionShortfall.of(refused, unnamed, unheld));
        if (!built.isEmpty()) {
            return new TermRealizations.Realization.Built(built, rest);
        }
        return unbuilt.came(rest, none("no containers of `" + place + "` this composed hold a"
                + " value as often as asked"));
    }

    /**
     * Containers inside the elements of another holding the value of an input as often as asked,
     * in all of them put end to end.
     *
     * <p>The values counted for are the keys', which the row fixed: they are not chosen here, and
     * each occurs nought times where the containers hold other values or none. Each is written as
     * many times as asked, spread over the containers ({@link NestedContainersAddingUp#alike}),
     * with values beside them that are none of them where the containers need more leaves than
     * they give. Keys the row fixed at one value are one value, counted once, and a count asked of
     * each of them is a count they all hold.
     */
    static TermRealizations.Realization composeAcrossContainersEqualToAKey(
            Type sourceType, List<List<String>> keptApart,
            List<RealizationTarget.OfANumber> targets,
            SequencedMap<RealizationTarget, AskedAt> demands, Quantities measuring,
            SearchRegion within, RuleReadingContext reading) {
        TermPath place = ((NumericTerm.OccurrencesOfAKey) targets.getFirst().term())
                .subjectPath();
        // Each value counted for, with every count asked of it.
        List<Place> values = new ArrayList<>();
        List<List<NumericSet>> wanted = new ArrayList<>();
        for (RealizationTarget.OfANumber each : targets) {
            NumericTerm.OccurrencesOfAKey term = (NumericTerm.OccurrencesOfAKey) each.term();
            AskedAt asked = demands.get(each);
            if (asked == null || asked.walking() == null) {
                return none("nothing says how often the value at `" + term.key()
                        + "` is to occur at `" + place + "`");
            }
            Place value = within == null ? null
                    : settled(within, new NumericTerm.ValueOf(term.key()));
            if (value == null) {
                return notChosen("`" + term.key() + "` stands at no one value, so what is counted"
                        + " for is not known");
            }
            int at = 0;
            while (at < values.size() && !values.get(at).sameAs(value)) {
                at++;
            }
            if (at == values.size()) {
                values.add(value);
                wanted.add(new ArrayList<>());
            }
            wanted.get(at).add(asked.walking());
        }
        List<TermPath> chain = place.containersHoldingIt();
        if (chain.size() < 2 || !place.equals(chain.getLast().element())) {
            return notChosen("a value at `" + place + "` is not an element of the container it"
                    + " stands inside, so the elements are chosen at a place inside them");
        }
        NumericTerm own = new NumericTerm.ValueOf(place);
        TermOrders orders = measuring.ordersOf(own);
        Carrier carrier = orders == null ? null : orders.observed();
        if (carrier == null) {
            return notChosen("a value at `" + place + "` is on no order its values are chosen on");
        }
        NumericDomain.Bounds run = switch (within.projectionOf(own)) {
            case NumericDomain.FormProjection.Within(NumericDomain.Bounds held) ->
                    held == null ? NumericDomain.Bounds.OPEN : held;
            case NumericDomain.FormProjection.NothingIsLeft _ -> null;
            case null -> NumericDomain.Bounds.OPEN;
        };
        if (run == null) {
            return none("the rules leave no value at `" + place + "`");
        }
        Set<CompositionCapacity> unheld = new LinkedHashSet<>();
        Set<CompositionRepertoire> unnamed = EnumSet.noneOf(CompositionRepertoire.class);
        List<Place> beside = new ArrayList<>();
        OfTheType leaves = OfTheType.of(
                NestedContainersAddingUp.ofTheLeaves(sourceType, place, reading), reading);
        for (Place each : valuesTheRulesLeave(carrier, run, leaves, unheld, unnamed,
                reading.today())) {
            if (values.stream().noneMatch(each::sameAs)) {
                beside.add(each);
            }
        }
        NestedContainersAddingUp nested = new NestedContainersAddingUp(place);
        ValuesCountedFor search = new ValuesCountedFor(values, wanted, run, beside,
                (counted, others) -> nested.alike(sourceType, keptApart, counted, others, carrier,
                        within, reading));
        search.counting(0, new ArrayList<>(), 0);
        Set<CompositionBudget> refused = EnumSet.noneOf(CompositionBudget.class);
        if (search.cutShort) {
            refused.add(CompositionBudget.ELEMENTS_A_COUNT_IS_COMPOSED_WITH);
        }
        if (search.spent) {
            refused.add(CompositionBudget.COUNTS_OF_KEYS_TRIED);
        }
        CompositionShortfall rest = search.rest.and(
                CompositionShortfall.of(refused, unnamed, unheld));
        if (!search.built.isEmpty()) {
            return new TermRealizations.Realization.Built(search.built, rest);
        }
        return search.unbuilt.came(rest, none("no containers of `" + place + "` this composed"
                + " hold the keys as often as asked"));
    }

    /**
     * The counts of several values tried one value at a time, each as often as every count asked of
     * it allows and the rules leave it a place, the leaves between them no more than a container
     * is composed with, and no more combinations than {@link #MOST_COUNTS_OF_KEYS}.
     *
     * <p>The combinations multiply with the keys, and a walk that built nothing is stopped by
     * neither the leaves nor the containers offered, which count what was built; so the
     * combinations tried are counted of their own.
     */
    static final class ValuesCountedFor {

        /** How a container is composed with the values counted and the others beside them. */
        interface Composes {

            TermRealizations.Realization compose(List<NestedContainersAddingUp.Counted> counted,
                                                 List<Place> others);
        }

        private final List<Place> values;
        private final List<List<NumericSet>> wanted;
        private final NumericDomain.Bounds run;
        private final List<Place> beside;
        private final Composes composes;
        final List<FixtureTemplate> built = new ArrayList<>();
        CompositionShortfall rest = CompositionShortfall.NONE;
        final UnbuiltAttempts unbuilt = new UnbuiltAttempts();
        boolean cutShort;
        boolean spent;
        int tried;

        /**
         * @param values the values counted for, no two alike
         * @param wanted the counts asked of each, in the order of {@code values}
         * @param run    the values the rules leave the place
         * @param beside the values that may stand beside them
         */
        ValuesCountedFor(List<Place> values, List<List<NumericSet>> wanted,
                         NumericDomain.Bounds run, List<Place> beside, Composes composes) {
            this.values = values;
            this.wanted = wanted;
            this.run = run;
            this.beside = beside;
            this.composes = composes;
        }

        /** Value {@code at} and those after it counted, {@code leaves} already given to the ones
         *  before. */
        void counting(int at, List<NestedContainersAddingUp.Counted> counted, int leaves) {
            if (built.size() >= MOST_OFFERED || spent) {
                return;
            }
            if (tried++ >= MOST_COUNTS_OF_KEYS) {
                spent = true;
                return;
            }
            if (at == values.size()) {
                composing(counted, leaves);
                return;
            }
            // A value occurs where the rules leave it at the place, and nowhere else.
            boolean mayOccur = run.admits(values.get(at));
            for (int often = 0; leaves + often <= MOST_ELEMENTS; often++) {
                final int asked = often;
                if ((often > 0 && !mayOccur) || !wanted.get(at).stream()
                        .allMatch(each -> each.holds(Count.of(asked), Carrier.WHOLE))) {
                    continue;
                }
                counted.add(new NestedContainersAddingUp.Counted(values.get(at), often));
                counting(at + 1, counted, leaves + often);
                counted.removeLast();
            }
            // A count past the most a container is composed with is asked and not tried.
            if (wanted.get(at).stream().anyMatch(each -> each.extent().max() == null
                    || each.extent().max().at().compareTo(Count.of(MOST_ELEMENTS)) > 0)) {
                cutShort = true;
            }
        }

        private void composing(List<NestedContainersAddingUp.Counted> counted, int leaves) {
            for (int extra = 0; extra <= beside.size() && leaves + extra <= MOST_ELEMENTS;
                    extra++) {
                if (tried++ >= MOST_COUNTS_OF_KEYS) {
                    spent = true;
                    return;
                }
                TermRealizations.Realization one =
                        composes.compose(List.copyOf(counted), beside.subList(0, extra));
                if (one instanceof TermRealizations.Realization.Built made) {
                    built.addAll(made.values());
                    rest = rest.and(made.rest());
                    return;
                }
                unbuilt.add(one);
            }
        }
    }

    /**
     * The values a count of how often one occurs may be composed with: those the rules leave the
     * place, and where {@code kept} keeps only some occurrences, of them the ones it keeps — a
     * value chosen to be counted is one the container's elements are kept for. Null where the
     * places the statement turns over at could not be worked out.
     */
    private static List<Place> valuesToCount(KeptOccurrences kept, NumericTerm own,
                                             TermPath container, TermPath place,
                                             Carrier carrier, NumericDomain.Bounds run,
                                             OfTheType element,
                                             Set<CompositionCapacity> unheld,
                                             Set<CompositionRepertoire> unnamed, Today today) {
        if (kept != null) {
            return keptValues(kept, own, container, place, carrier, run, element, unheld,
                    unnamed, today);
        }
        return valuesTheRulesLeave(carrier, run, element, unheld, unnamed, today);
    }

    /**
     * The values that may stand beside the one counted: any the rules leave the place, kept by
     * the statement or not, since a value other than the counted one adds nothing to its count.
     */
    private static List<Place> valuesBeside(Place counted, List<Place> toCount, KeptOccurrences kept,
                                            Carrier carrier, NumericDomain.Bounds run,
                                            OfTheType element,
                                            Set<CompositionCapacity> unheld,
                                            Set<CompositionRepertoire> unnamed, Today today) {
        List<Place> pool = kept == null ? toCount
                : valuesTheRulesLeave(carrier, run, element, unheld, unnamed, today);
        return pool.stream().filter(each -> !each.sameAs(counted)).toList();
    }

    /** Values of an element of {@code element} inside {@code run}, near where a value of the place
     *  is usually near on {@code today}. */
    private static List<Place> valuesTheRulesLeave(Carrier carrier, NumericDomain.Bounds run,
                                                   OfTheType element,
                                                   Set<CompositionCapacity> unheld,
                                                   Set<CompositionRepertoire> unnamed,
                                                   Today today) {
        return carrier.counts()
                ? valuesAlong(carrier, run, List.of(), MOST_ELEMENTS + 1,
                        carrier.usualPlace(today), unheld, unnamed)
                : valuesAlongAnOrder(carrier, run, List.of(), MOST_ELEMENTS + 1, element,
                        unnamed);
    }

    /**
     * The type a value named along an order that is not counted is a value of, so that what is
     * named is one a row can hold.
     *
     * <p>The order knows nothing of the type. Walked from where a run starts nowhere, the first
     * string is the empty one, and a rule giving each label a letter refuses every row holding
     * it; a string the type's rules refuse is no value of the place however it lies along the
     * order. So a value the order names is offered where the type admits it, and inside a run
     * where it admits none of those, strings the type admits there are: first those written for
     * a value of the type wherever it stands, so a row holds the one the other rows hold, then
     * those its rules leave inside the run ({@link Partitions#stringsTheRulesLeave}).
     *
     * @param strings what the type's rules leave its strings, or null where they leave every one
     *                or nothing is known of the type, and every value the order names is offered
     * @param written the strings written for values of the type ({@link Witnesses#stringsOf}),
     *                which its rules admit
     */
    record OfTheType(Partitions.StringsTheRulesLeave strings, List<String> written) {

        OfTheType {
            written = List.copyOf(written);
        }

        /** Nothing known of the type, so every value the order names. */
        static final OfTheType ANY = new OfTheType(null, List.of());

        /** {@code type} read whole, its rules read by {@code reading}; any where it is null. */
        static OfTheType of(Type type, RuleReadingContext reading) {
            if (type == null) {
                return ANY;
            }
            RuleReadingSource source = reading.source();
            return of(TypeView.of(type, source.inners(), source.symbols(), source.kinds(),
                    source.sums()), reading);
        }

        /** The type {@code view} reads, its rules read by {@code reading}. */
        static OfTheType of(TypeView view, RuleReadingContext reading) {
            Partitions.StringsTheRulesLeave strings = Partitions.stringsTheRulesLeave(view, reading);
            return strings == null ? ANY : new OfTheType(strings,
                    Witnesses.stringsOf(view.declared(), MOST_ELEMENTS + 1, reading).stream()
                            .filter(strings::admits).toList());
        }

        /**
         * The same, where as many different values of it as elements are to be offered: with
         * the strings written for a value of the type offered whatever its rules leave, since
         * the order names one string where nothing bounds it and elements apart at a place hold
         * a different one each.
         */
        static OfTheType manyOf(TypeView view, RuleReadingContext reading) {
            Partitions.StringsTheRulesLeave strings = Partitions.stringsTheRulesLeave(view, reading);
            return new OfTheType(strings,
                    Witnesses.stringsOf(view.declared(), MOST_ELEMENTS + 1, reading).stream()
                            .filter(each -> strings == null || strings.admits(each)).toList());
        }

        /** Whether {@code place} is a value of the type: a string its rules admit, or any place
         *  of an order that holds no strings. */
        boolean admits(Place place) {
            return strings == null || !(place instanceof Text text) || strings.admits(text.at());
        }

        /** Up to {@code many} strings the type admits between {@code low} and {@code high}. */
        List<Place> inside(Endpoint low, Endpoint high, int many) {
            NumericDomain.Bounds run = new NumericDomain.Bounds(low, high);
            List<Place> out = new ArrayList<>();
            for (String each : written) {
                if (out.size() < many && run.admits(Text.of(each))) {
                    out.add(Text.of(each));
                }
            }
            if (strings == null) {
                return out;
            }
            for (String each : strings.inside(low, high, many - out.size())) {
                if (out.stream().noneMatch(Text.of(each)::sameAs)) {
                    out.add(Text.of(each));
                }
            }
            return out;
        }
    }

    /**
     * The values near the places {@code kept}'s statement turns over at that the statement keeps,
     * each put to it as the one element of {@code container}, or null where the places it turns
     * over at could not be worked out.
     */
    private static List<Place> keptValues(KeptOccurrences kept, NumericTerm own,
                                          TermPath container, TermPath place, Carrier carrier,
                                          NumericDomain.Bounds run, OfTheType element,
                                          Set<CompositionCapacity> unheld,
                                          Set<CompositionRepertoire> unnamed, Today today) {
        List<Place> near;
        if (carrier.counts()) {
            List<ExactRatio> turns = kept.perElement().turnsAt(own, Map.of());
            if (turns == null) {
                return null;
            }
            near = valuesAlong(carrier, run, turns, MOST_ELEMENTS + 1,
                    UsualPlaces.of(own, carrier, today), unheld, unnamed);
        } else {
            List<Place> turns = kept.perElement().placesTurnedAt(own, Map.of());
            if (turns == null) {
                return null;
            }
            near = valuesAlongAnOrder(carrier, run, turns, MOST_ELEMENTS + 1, element, unnamed);
        }
        List<Place> out = new ArrayList<>();
        for (Place each : near) {
            BorderQuantity.Observation row = new AnElementRead(container, place, Map.of(),
                    List.of(carrier.valueOf(each)));
            if (kept.perElement().at(row) instanceof AStatementAtARow.Answer.Holds) {
                out.add(each);
            }
        }
        return out;
    }

    /** Whether some value of {@code values} occurs as often as {@code wanted} holds. */
    private static boolean occursAsOften(List<Place> values, NumericSet wanted) {
        for (Place each : values) {
            long same = values.stream().filter(each::sameAs).count();
            if (wanted.holds(Count.of(same), Carrier.WHOLE)) {
                return true;
            }
        }
        return false;
    }

    /**
     * One thing the elements of the container are asked, and how many of them are to answer it.
     *
     * <p>Two kinds, and one walk over both. How many elements meet a statement is a count; an
     * element standing at a value the row placed there is some element being one of a set. Both
     * are a question each value answers and a number of the elements that answer it, so a container
     * composed for both is composed by sharing elements out among what they answer together.
     */
    private sealed interface Asked {

        /** Whether {@code value}, as the element {@code row} reads, answers this. */
        AStatementAtARow.Answer at(Place value, BorderQuantity.Observation row);

        /** Whether a container with {@code meeting} elements answering this has as many as this
         *  asks. */
        boolean asMany(int meeting);

        /** Where an element's answer to this turns over, with the numbers beside it where {@code
         *  beside} says; null where that could not be worked out. */
        List<ExactRatio> turnsAt(NumericTerm element, Map<NumericTerm, Place> beside);

        /** The places an element turns over at, where its values are ordered and not counted, with
         *  the positions beside it where {@code beside} says; null where that could not be worked
         *  out. */
        List<Place> placesTurnedAt(NumericTerm element, Map<NumericTerm, Place> beside);

        /** Whether a container of {@code values}, read whole as {@code row}, has as many elements
         *  answering this as it asks — for every count the reading leaves, where one was not read. */
        AStatementAtARow.Answer over(TermPath container, List<Place> values,
                                     BorderQuantity.Observation row);

        /**
         * How many this counts among the elements of {@code container} {@code row} holds: the
         * least, and how many more where something could not be read — or null where the walk
         * could not reach the container.
         */
        AStatementAtARow.HowManyAtARow among(TermPath container, BorderQuantity.Observation row);

        /** Whether what an element of {@code container} answers of this may turn on which value
         *  stands at {@code at} inside it ({@link AStatementAtARow#readsTheValueAt}). */
        boolean readsTheValueAt(TermPath container, TermPath at);
        /** What an element of {@code container} answers of this turns on, the elements held as
         *  groups under one value at {@code under}, or each on its own where it is null
         *  ({@link AStatementAtARow#turnsOnAmong}). */
        AStatementAtARow.TurnsOn turnsOnAmong(TermPath container, TermPath under);

        /** How many elements meet {@code perElement}: one of the counts {@code wanted} holds. */
        record SoManyMeeting(AStatementAtARow perElement, LevelRegion wanted,
                             Optional<TermPath> differentAt) implements Asked {

            @Override
            public AStatementAtARow.Answer at(Place value, BorderQuantity.Observation row) {
                return perElement.at(row);
            }

            /** Read the way the row's own reading reads the count: of the elements, or of the
             *  different values they hold where that is what is counted. */
            @Override
            public AStatementAtARow.Answer over(TermPath container, List<Place> values,
                                                BorderQuantity.Observation row) {
                AStatementAtARow.HowManyAtARow counted = among(container, row);
                return counted == null
                        ? new AStatementAtARow.Answer.CouldNotTell(Set.of(ReadingGap.COULD_NOT_WALK))
                        : counted.whether(n -> ExactAnswer.held(asMany(n)));
            }

            /** The elements meeting the statement, or the different values they hold where that
             *  is what is counted — of the one container composed, which is every element there
             *  is where a count is of all the containers inside the elements of another put end
             *  to end ({@link #composeAcross}). */
            @Override
            public AStatementAtARow.HowManyAtARow among(TermPath container,
                                                        BorderQuantity.Observation row) {
                return perElement.howManyIn(container, differentAt, Optional.empty(), row);
            }

            @Override
            public boolean readsTheValueAt(TermPath container, TermPath at) {
                return perElement.readsTheValueAt(container, at);
            }
            @Override
            public AStatementAtARow.TurnsOn turnsOnAmong(TermPath container, TermPath under) {
                return perElement.turnsOnAmong(container, under);
            }

            @Override
            public boolean asMany(int meeting) {
                return wanted.contains(new Level.OfTheQuantity(ExactRatio.of(meeting)));
            }

            @Override
            public List<ExactRatio> turnsAt(NumericTerm element, Map<NumericTerm, Place> beside) {
                return perElement.turnsAt(element, beside);
            }

            @Override
            public List<Place> placesTurnedAt(NumericTerm element, Map<NumericTerm, Place> beside) {
                return perElement.placesTurnedAt(element, beside);
            }
        }

        /**
         * Some element whose number at {@code at}, a position inside it, stands in {@code set} on
         * the order {@code on} — what a row placing a number inside an element asks, where the
         * elements are chosen among the values each is read at whole.
         */
        record SomeElementAt(TermPath at, NumericSet set, Carrier on) implements Asked {

            /** Whether the element {@code row} is read as holds a number at {@code at} in the
             *  set; failing where it holds nothing there. */
            AStatementAtARow.Answer ofAnElement(BorderQuantity.Observation row) {
                return switch (row.at(at)) {
                    case WalkResult.CouldNotWalk<ObservationAtPoint> _ ->
                            new AStatementAtARow.Answer.CouldNotTell(
                                    Set.of(ReadingGap.COULD_NOT_WALK));
                    case WalkResult.Reached(ObservationAtPoint.Value(ObservedValue value)) -> {
                        Place place = on.placeOf(value);
                        yield place == null
                                ? new AStatementAtARow.Answer.CouldNotTell(
                                        Set.of(ReadingGap.COULD_NOT_WALK))
                                : set.holds(place, on) ? AStatementAtARow.Answer.HOLDS
                                        : AStatementAtARow.Answer.FAILS;
                    }
                    case WalkResult.Reached<ObservationAtPoint> _ -> AStatementAtARow.Answer.FAILS;
                };
            }

            @Override
            public AStatementAtARow.Answer at(Place value, BorderQuantity.Observation row) {
                return ofAnElement(row);
            }

            @Override
            public boolean asMany(int meeting) {
                return meeting >= 1;
            }

            @Override
            public AStatementAtARow.Answer over(TermPath container, List<Place> values,
                                                BorderQuantity.Observation row) {
                if (!(row.eachElementOf(container) instanceof WalkResult.Reached<
                        List<BorderQuantity.Observation>>(var elements))) {
                    return new AStatementAtARow.Answer.CouldNotTell(
                            Set.of(ReadingGap.COULD_NOT_WALK));
                }
                for (BorderQuantity.Observation each : elements) {
                    if (ofAnElement(each) instanceof AStatementAtARow.Answer.Holds) {
                        return AStatementAtARow.Answer.HOLDS;
                    }
                }
                return AStatementAtARow.Answer.FAILS;
            }

            /** The elements whose number stands in the set. */
            @Override
            public AStatementAtARow.HowManyAtARow among(TermPath container,
                                                        BorderQuantity.Observation row) {
                if (!(row.eachElementOf(container) instanceof WalkResult.Reached<
                        List<BorderQuantity.Observation>>(var elements))) {
                    return null;
                }
                int meet = 0;
                int unread = 0;
                Set<ReadingGap> why = new LinkedHashSet<>();
                for (BorderQuantity.Observation each : elements) {
                    switch (ofAnElement(each)) {
                        case AStatementAtARow.Answer.Holds _ -> meet++;
                        case AStatementAtARow.Answer.Fails _ -> { }
                        case AStatementAtARow.Answer.CouldNotTell(var stopped) -> {
                            unread++;
                            why.addAll(stopped);
                        }
                    }
                }
                return new AStatementAtARow.HowManyAtARow(meet, unread, why);
            }

            /** Where the number this asks of is that place, inside it or holds it. */
            @Override
            public boolean readsTheValueAt(TermPath container, TermPath place) {
                return at.isAtOrUnder(place) || place.isAtOrUnder(at);
            }
            /** A number at one place inside the element. */
            @Override
            public AStatementAtARow.TurnsOn turnsOnAmong(TermPath container, TermPath under) {
                return AStatementAtARow.TurnsOn.THE_ELEMENT;
            }

            /** Where standing in the set turns over, which the set says
             *  ({@link NumericSet#turnsAt}), for the number this is about. */
            @Override
            public List<ExactRatio> turnsAt(NumericTerm element, Map<NumericTerm, Place> beside) {
                return element.subjectPath().equals(at)
                        ? set.turnsAt().stream().map(turn -> Count.number(turn).exactly()).toList()
                        : List.of();
            }

            /** The same on an order with no numbers, where the places are the answer. */
            @Override
            public List<Place> placesTurnedAt(NumericTerm element, Map<NumericTerm, Place> beside) {
                return element.subjectPath().equals(at) ? set.turnsAt() : List.of();
            }
        }

        /** Some element standing in {@code set}, on the order the element is written on. */
        record SomeElementIn(NumericSet set, Carrier on) implements Asked {

            @Override
            public AStatementAtARow.Answer at(Place value, BorderQuantity.Observation row) {
                return set.holds(value, on) ? AStatementAtARow.Answer.HOLDS
                        : AStatementAtARow.Answer.FAILS;
            }

            @Override
            public boolean asMany(int meeting) {
                return meeting >= 1;
            }

            @Override
            public AStatementAtARow.Answer over(TermPath container, List<Place> values,
                                                BorderQuantity.Observation row) {
                return values.stream().anyMatch(value -> set.holds(value, on))
                        ? AStatementAtARow.Answer.HOLDS : AStatementAtARow.Answer.FAILS;
            }

            /** Asked of the values chosen and not of a row: an element that is one number is
             *  chosen as one, and never among the values it is read at whole. */
            @Override
            public AStatementAtARow.HowManyAtARow among(TermPath container,
                                                        BorderQuantity.Observation row) {
                throw new IllegalStateException(
                        "an element standing in a set is one number, and is chosen as one");
            }

            /** The element is the number this asks of, whatever place is asked about. */
            @Override
            public boolean readsTheValueAt(TermPath container, TermPath at) {
                return true;
            }
            /** The element itself. */
            @Override
            public AStatementAtARow.TurnsOn turnsOnAmong(TermPath container, TermPath under) {
                return AStatementAtARow.TurnsOn.THE_ELEMENT;
            }

            /** Where standing in the set turns over, which the set says ({@link NumericSet#turnsAt}). */
            @Override
            public List<ExactRatio> turnsAt(NumericTerm element, Map<NumericTerm, Place> beside) {
                return set.turnsAt().stream().map(at -> Count.number(at).exactly()).toList();
            }

            /** The same on an order with no numbers, where the places are the answer. */
            @Override
            public List<Place> placesTurnedAt(NumericTerm element, Map<NumericTerm, Place> beside) {
                return set.turnsAt();
            }
        }
    }

    /**
     * The number the statements read at each element, and the numbers they read beside it.
     *
     * @param term    the element's own number, which is the element itself
     * @param carrier the order the element is written on
     * @param beside  every number the statements read that stands at one place of the row, in the
     *                order they were met
     * @param on      the order each number the statements read is written on
     */
    private record Element(NumericTerm term, Carrier carrier, List<NumericTerm> beside,
                           Map<NumericTerm, Carrier> on) {

        /**
         * The element of {@code container} as every count reads it, or null where one of them
         * reads it as something other than one number standing at the element itself.
         *
         * <p>A number of another container's elements is not beside the element: it is read
         * element by element where the statement is asked, which is where it is left.
         */
        static Element of(List<RealizationTarget.ACount> counts, TermPath container) {
            NumericTerm own = null;
            Set<NumericTerm> beside = new LinkedHashSet<>();
            Map<NumericTerm, Carrier> on = new LinkedHashMap<>();
            for (RealizationTarget.ACount each : counts) {
                on.putAll(each.count().on());
                for (NumericTerm term : each.count().numbers()) {
                    if (term.subjectPath().isAtOrUnder(container.element())) {
                        if (!(term instanceof NumericTerm.ValueOf)
                                || !term.subjectPath().equals(container.element())
                                || (own != null && !own.equals(term))) {
                            return null;
                        }
                        own = term;
                    } else if (!term.subjectPath().insideAContainer()) {
                        beside.add(term);
                    }
                }
            }
            Carrier carrier = own == null ? null : on.get(own);
            if (carrier == null) {
                return null;
            }
            return new Element(own, carrier, List.copyOf(beside), on);
        }
    }

    /**
     * What a row holds at the position of {@code term} once the number stands at {@code at}, put
     * in {@code written} — nothing where the number is not what the position holds.
     *
     * <p>A position holds the number only of a term that is the position's own value. A number
     * taken of the position, the year of a date, stands at a place on the order its answer is
     * measured on, and a value written at the position from it would be a whole number where a date
     * is: the value of such a position is another term's to construct, and a statement reading it
     * is one the row cannot yet be asked.
     */
    private static void writtenAt(NumericTerm term, Place at, Quantities measuring,
                                  Map<TermPath, ObservedValue> written) {
        if (!(term instanceof NumericTerm.ValueOf)) {
            return;
        }
        TermOrders orders = measuring.ordersOf(term);
        Carrier on = orders == null ? null : orders.observed();
        if (on != null) {
            written.put(term.subjectPath(), on.valueOf(at));
        }
    }

    /**
     * The numbers {@code asked} reads that stand outside every container, each at the one value
     * the region leaves it at, and the value it is written as in {@code written}; a number the
     * region leaves at more or none, or that stands on no order, is in neither.
     */
    private static Map<NumericTerm, Place> settledOutside(List<Asked> asked,
                                                          Quantities measuring,
                                                          SearchRegion within,
                                                          Map<TermPath, ObservedValue> written) {
        Map<NumericTerm, Place> out = new LinkedHashMap<>();
        for (Asked one : asked) {
            if (!(one instanceof Asked.SoManyMeeting(AStatementAtARow perElement, _, _))) {
                continue;
            }
            for (NumericTerm term : perElement.numbers()) {
                if (term.subjectPath().insideAContainer()) {
                    continue;
                }
                Place at = settled(within, term);
                if (at != null) {
                    out.put(term, at);
                    writtenAt(term, at, measuring, written);
                }
            }
        }
        return out;
    }

    /**
     * The values an element of a container is chosen among, listed holding one value at
     * {@code place} at a time: the values {@code place} is chosen at, the listing holding the
     * first of them, and the listing holding any of them by its place among them.
     */
    private record ListedByValue(List<ObservedValue> values, ElementValues first,
                                 IntFunction<List<ObservedValue>> under) {}

    /**
     * The values of the element of {@code container}, of type {@code element}, listed holding one
     * value at {@code place} at a time — or null where some part has no values to choose among.
     *
     * <p>Each part is chosen at what {@code numbers} says, and {@code place} at what
     * {@code valuesThere} says, one value of it for each listing. The listings are alike but for
     * that one value, so an element of one stands where the same element of another does.
     */
    private static ListedByValue listedByValue(
            TermPath container, Type element, RuleReadingContext reading, TermPath place,
            BiFunction<TermPath, TypeView, List<ObservedValue>> numbers,
            BiFunction<TermPath, TypeView, List<ObservedValue>> valuesThere) {
        List<List<ObservedValue>> valuesAt = new ArrayList<>();
        ElementValues first = ElementValues.of(container, element, reading, (at, part) -> {
            if (!at.equals(place)) {
                return numbers.apply(at, part);
            }
            List<ObservedValue> values = valuesThere.apply(at, part);
            if (values == null || values.isEmpty()) {
                return values;
            }
            valuesAt.add(values);
            return List.of(values.getFirst());
        });
        if (first == null) {
            return null;
        }
        List<ObservedValue> values = valuesAt.isEmpty() ? List.of() : valuesAt.getFirst();
        return new ListedByValue(values, first, value -> {
            if (value == 0) {
                return first.listed().values();
            }
            ElementValues holdingIt = ElementValues.of(container, element, reading,
                    (at, part) -> at.equals(place) ? List.of(values.get(value))
                            : numbers.apply(at, part));
            return holdingIt == null ? List.of() : holdingIt.listed().values();
        });
    }

    /**
     * A group of the elements of a container under one value at the place whose different values
     * are counted: which value, as its place among those the place is chosen at, and which of the
     * elements listed holding that value it holds, as their places in that listing — one place
     * again where it holds one element twice.
     */
    private record HeldUnder(int value, List<Integer> picked) {

        HeldUnder {
            picked = List.copyOf(picked);
        }
    }

    /**
     * The groups of the elements of a container under one value at the place whose different
     * values are counted, and the containers drawn of them.
     *
     * <p>What one group is to a count is what a row holding it alone has of it. How many different
     * values meet a statement is one or none — the value is counted or not, whatever the statement
     * is asked of — and how many elements meet one is how many of the group's do. So a container of
     * several groups, no two under one value, has of every count what they have between them, and
     * the sharings count it that way ({@link Sharing}).
     *
     * <p>Which value a group is under is apart from what its elements are: the elements are
     * listed holding one value at the place, and a group drawn under another is the same elements
     * listed holding that one. Where nothing asked reads the value itself — only which elements
     * hold one value, as how often it occurs and what they come to do — a group answers alike
     * under every value, so the groups are listed under the first and a container draws each
     * under a value of its own. Where something does, they are listed under each value, and which
     * group takes which value is a matching.
     */
    private static final class UnderEachValue {

        private final int values;
        private final IntFunction<List<ObservedValue>> listedUnder;
        private final Map<Integer, List<ObservedValue>> listed = new HashMap<>();
        private final boolean alike;
        private Groups<HeldUnder> groups;
        private final List<Set<Integer>> under = new ArrayList<>();

        private UnderEachValue(int values, IntFunction<List<ObservedValue>> listedUnder,
                               boolean alike) {
            this.values = values;
            this.listedUnder = listedUnder;
            this.alike = alike;
        }

        /**
         * Every group of the elements listed under one of {@code values} values, by what each
         * comes to of every one of {@code asked}, without those a count asking for none of what
         * they meet rules out: those holding one element first, then two, and so on — no more of
         * them than the values an element is chosen among, which is the figure put in
         * {@code refused} where it stops the listing. A group a count could not be read at is in
         * none, and what kept it out is said.
         *
         * @param listedUnder the elements listed holding the value at its place among them
         * @param once        no element is held twice, which elements their rules keep apart are
         *                    not
         * @param oneEach     a value is held by one element and no more, which elements their
         *                    rules keep apart at the place are
         */
        static UnderEachValue of(int values, IntFunction<List<ObservedValue>> listedUnder,
                                 Function<List<ObservedValue>, BorderQuantity.Observation> holding,
                                 TermPath container, TermPath at, List<Asked> asked, boolean once,
                                 boolean oneEach, Set<CompositionBudget> refused) {
            boolean alike = asked.stream().noneMatch(each -> each.readsTheValueAt(container, at));
            boolean byItsElements = readOffItsElements(asked, container, at);
            UnderEachValue out = new UnderEachValue(values, listedUnder, alike);
            Groups<HeldUnder> every = Groups.none();
            // What each listed element comes to alone, by the value it is listed under: read once
            // and put together for every group holding it, where that is what a group comes to.
            Map<Integer, List<AStatementAtARow.HowManyAtARow[]>> alone = new HashMap<>();
            int[] left = {CompositionBudget.VALUES_AN_ELEMENT_IS_CHOSEN_AMONG.maximum()};
            listing:
            for (int size = 1; size <= (oneEach ? 1 : MOST_ELEMENTS); size++) {
                boolean some = false;
                for (int value = 0; value < (alike ? Math.min(values, 1) : values); value++) {
                    List<ObservedValue> of = out.listing(value);
                    int under = value;
                    List<AStatementAtARow.HowManyAtARow[]> each = !byItsElements ? null
                            : alone.computeIfAbsent(value, v -> eachAlone(of, holding, container,
                                    asked));
                    boolean walked = eachChoice(of.size(), size, !once, picked -> {
                        if (left[0]-- == 0) {
                            return false;
                        }
                        List<Integer> places = new ArrayList<>();
                        List<ObservedValue> elements = new ArrayList<>();
                        for (int one : picked) {
                            places.add(one);
                            elements.add(of.get(one));
                        }
                        HeldUnder group = new HeldUnder(under, places);
                        if (byItsElements) {
                            addOfItsElements(every, group, each, asked);
                        } else {
                            add(every, group, holding.apply(elements), container, asked);
                        }
                        return true;
                    });
                    // A choice was turned away for the figure, which is the one thing that does.
                    if (!walked) {
                        refused.add(CompositionBudget.VALUES_AN_ELEMENT_IS_CHOSEN_AMONG);
                        break listing;
                    }
                    some |= once ? of.size() >= size : !of.isEmpty();
                }
                if (!some) {
                    break;
                }
            }
            out.groups = every.keptBy(asked);
            for (List<HeldUnder> kind : out.groups.values()) {
                Set<Integer> held = new LinkedHashSet<>();
                kind.forEach(each -> held.add(each.value()));
                out.under.add(held);
            }
            return out;
        }

        /** The groups, by what each comes to of every count. */
        Groups<HeldUnder> groups() {
            return groups;
        }

        /** How many groups of the {@code kind}-th kind one container may hold: one under each
         *  value they may be drawn under. */
        int capacity(int kind) {
            return alike ? values : under.get(kind).size();
        }

        /** The elements listed holding the value at its place among those the place is chosen
         *  at, listed once. */
        private List<ObservedValue> listing(int value) {
            return listed.computeIfAbsent(value, listedUnder::apply);
        }

        /** {@code group}, which {@code row} holds alone, put with those coming to what it does
         *  of every count, or in none where one could not be read. */
        private static void add(Groups<HeldUnder> into, HeldUnder group,
                                BorderQuantity.Observation row, TermPath container,
                                List<Asked> asked) {
            int[] counted = new int[asked.size()];
            for (int i = 0; i < asked.size(); i++) {
                AStatementAtARow.HowManyAtARow read = asked.get(i).among(container, row);
                if (read == null) {
                    into.unread().add(ReadingGap.COULD_NOT_WALK);
                    return;
                }
                if (read.unread() > 0) {
                    into.unread().addAll(read.why());
                    return;
                }
                counted[i] = read.meet();
            }
            into.add(group, group.picked().size(), counted);
        }

        /**
         * Whether what a group of the elements of {@code container} under one value at {@code at}
         * comes to of every one of {@code asked} is what its elements come to alone, put together:
         * what each element answers turns on the element alone, and every count is of the
         * elements meeting a statement or of the different values at {@code at} they hold — one
         * value for the whole group, held where some element of it meets the statement.
         */
        private static boolean readOffItsElements(List<Asked> asked, TermPath container,
                                                  TermPath at) {
            for (Asked each : asked) {
                if (each.turnsOnAmong(container, at) != AStatementAtARow.TurnsOn.THE_ELEMENT) {
                    return false;
                }
                if (each instanceof Asked.SoManyMeeting(var _, var _,
                        Optional<TermPath> differentAt)
                        && differentAt.isPresent() && !differentAt.get().equals(at)) {
                    return false;
                }
            }
            return true;
        }

        /** What each of {@code of} comes to of every one of {@code asked}, read at a row holding
         *  it alone — null where the walk could not reach the container. */
        private static List<AStatementAtARow.HowManyAtARow[]> eachAlone(
                List<ObservedValue> of,
                Function<List<ObservedValue>, BorderQuantity.Observation> holding,
                TermPath container, List<Asked> asked) {
            List<AStatementAtARow.HowManyAtARow[]> out = new ArrayList<>();
            for (ObservedValue element : of) {
                BorderQuantity.Observation row = holding.apply(List.of(element));
                AStatementAtARow.HowManyAtARow[] read =
                        new AStatementAtARow.HowManyAtARow[asked.size()];
                for (int i = 0; i < asked.size(); i++) {
                    read[i] = asked.get(i).among(container, row);
                }
                out.add(read);
            }
            return out;
        }

        /**
         * {@code group} put with those coming to what it does of every count, as its elements
         * come to it alone ({@link #readOffItsElements}): as many as meet a statement, or one value
         * where some element meets it and none where none does — or in none where one could not
         * be read.
         */
        private static void addOfItsElements(Groups<HeldUnder> into, HeldUnder group,
                                             List<AStatementAtARow.HowManyAtARow[]> alone,
                                             List<Asked> asked) {
            int[] counted = new int[asked.size()];
            for (int i = 0; i < asked.size(); i++) {
                boolean ofTheValue = asked.get(i) instanceof Asked.SoManyMeeting(var _, var _,
                        Optional<TermPath> differentAt) && differentAt.isPresent();
                int meet = 0;
                int unread = 0;
                Set<ReadingGap> why = new LinkedHashSet<>();
                for (int one : group.picked()) {
                    AStatementAtARow.HowManyAtARow read = alone.get(one)[i];
                    if (read == null) {
                        into.unread().add(ReadingGap.COULD_NOT_WALK);
                        return;
                    }
                    meet = ofTheValue ? Math.max(meet, read.meet()) : meet + read.meet();
                    unread = ofTheValue ? Math.max(unread, read.unread()) : unread + read.unread();
                    why.addAll(read.why());
                }
                if (ofTheValue && meet > 0) {
                    unread = 0;
                }
                if (unread > 0) {
                    into.unread().addAll(why);
                    return;
                }
                counted[i] = meet;
            }
            into.add(group, group.picked().size(), counted);
        }

        /**
         * Hands {@code take} every choice of {@code size} of {@code of} things, as the places of
         * those chosen in order, the same place again where {@code repeats}; until it answers
         * that it has had enough.
         *
         * @return whether every choice was handed over
         */
        private static boolean eachChoice(int of, int size, boolean repeats,
                                          Predicate<int[]> take) {
            if (of == 0 || (!repeats && of < size)) {
                return true;
            }
            int[] picked = new int[size];
            for (int i = 0; i < size; i++) {
                picked[i] = repeats ? 0 : i;
            }
            while (true) {
                if (!take.test(picked.clone())) {
                    return false;
                }
                int i = size - 1;
                while (i >= 0 && picked[i] == (repeats ? of - 1 : of - size + i)) {
                    i--;
                }
                if (i < 0) {
                    return true;
                }
                picked[i]++;
                for (int j = i + 1; j < size; j++) {
                    picked[j] = repeats ? picked[i] : picked[j - 1] + 1;
                }
            }
        }

        /**
         * Whether the rules of the container at {@code container} keep its elements apart at
         * {@code at}, so that no value there is held by two of them: one of the places they are
         * kept apart at, {@code apart}, is that place, as fields from the element.
         */
        static boolean oneEachUnder(TermPath container, TermPath at, List<List<String>> apart) {
            ElementProjection below = ElementProjection.below(container.element(), at);
            if (below == null) {
                return false;
            }
            List<String> fields = new ArrayList<>();
            for (TermPath.Step each : below.steps()) {
                if (!(each instanceof TermPath.Step.Field(String name))) {
                    return false;
                }
                fields.add(name);
            }
            return apart.contains(fields);
        }

        /**
         * The elements of so many groups of each kind as {@code share} asks, no two of them under
         * one value — or null where no choice of values is that.
         *
         * <p>Where every group answers alike under any value, each group taken is drawn under the
         * next value. Otherwise which group takes which value is a matching of the groups asked
         * for to the values each kind holds groups under, found by turning a value over to another
         * group where the one holding it can take another: a value taken first by a kind that
         * could have taken others is no reason a kind holding only that value goes without.
         */
        List<ObservedValue> drawn(int[] share) {
            List<Integer> kindOf = new ArrayList<>();
            for (int g = 0; g < share.length; g++) {
                for (int n = 0; n < share[g]; n++) {
                    kindOf.add(g);
                }
            }
            int[] valueOf = new int[kindOf.size()];
            if (alike) {
                if (kindOf.size() > values) {
                    return null;
                }
                for (int slot = 0; slot < kindOf.size(); slot++) {
                    valueOf[slot] = slot;
                }
            } else {
                Map<Integer, Integer> takenBy = new HashMap<>();
                for (int slot = 0; slot < kindOf.size(); slot++) {
                    if (!matched(slot, kindOf, takenBy, new HashSet<>())) {
                        return null;
                    }
                }
                takenBy.forEach((value, slot) -> valueOf[slot] = value);
            }
            List<ObservedValue> out = new ArrayList<>();
            for (int slot = 0; slot < kindOf.size(); slot++) {
                HeldUnder group = null;
                for (HeldUnder each : groups.values().get(kindOf.get(slot))) {
                    if (alike || each.value() == valueOf[slot]) {
                        group = each;
                        break;
                    }
                }
                // Listed under another value, the elements stand where they stood under the first:
                // only the value differs, and a listing that came out otherwise is drawn from none.
                List<ObservedValue> of = listing(valueOf[slot]);
                if (group == null || (alike && of.size() != listing(0).size())) {
                    return null;
                }
                for (int one : group.picked()) {
                    out.add(of.get(one));
                }
            }
            return out;
        }

        private boolean matched(int slot, List<Integer> kindOf, Map<Integer, Integer> takenBy,
                                Set<Integer> tried) {
            for (int value : under.get(kindOf.get(slot))) {
                if (!tried.add(value)) {
                    continue;
                }
                Integer holder = takenBy.get(value);
                if (holder == null || matched(holder, kindOf, takenBy, tried)) {
                    takenBy.put(value, slot);
                    return true;
                }
            }
            return false;
        }
    }

    /** {@code row}, with {@code written} in it where there is any: a row asked once for each way
     *  the elements are shared out is not wrapped for nothing. */
    private static BorderQuantity.Observation withNumbersBeside(
            BorderQuantity.Observation row, Map<TermPath, ObservedValue> written) {
        return written.isEmpty() ? row : new WithNumbersBeside(row, written);
    }

    /**
     * A row with the numbers beside its elements written at the values they were fixed at, which
     * a row of the container alone does not hold.
     */
    private record WithNumbersBeside(BorderQuantity.Observation holding,
                                     Map<TermPath, ObservedValue> written)
            implements BorderQuantity.Observation {

        @Override
        public WalkResult<ObservationAtPoint> at(TermPath path) {
            ObservedValue value = written.get(path);
            return value == null ? holding.at(path)
                    : WalkResult.reached(new ObservationAtPoint.Value(value));
        }

        @Override
        public WalkResult<List<ObservedValue>> everyValueAt(TermPath path) {
            return holding.everyValueAt(path);
        }

        @Override
        public WalkResult<List<BorderQuantity.Observation>> eachElementOf(TermPath of) {
            return switch (holding.eachElementOf(of)) {
                case WalkResult.CouldNotWalk<List<BorderQuantity.Observation>> _ ->
                        WalkResult.couldNotWalk();
                case WalkResult.Reached<List<BorderQuantity.Observation>>(var elements) ->
                        WalkResult.reached(elements.stream()
                                .<BorderQuantity.Observation>map(each ->
                                        new WithNumbersBeside(each, written))
                                .toList());
            };
        }
    }

    /** The one place the region leaves {@code term} at, or null where it leaves more or none. */
    static Place settled(SearchRegion within, NumericTerm term) {
        if (!(within.projectionOf(term)
                instanceof NumericDomain.FormProjection.Within(NumericDomain.Bounds held))
                || held == null || held.min() == null || held.max() == null
                || !held.min().inclusive() || !held.max().inclusive()
                || !held.min().at().sameAs(held.max().at())) {
            return null;
        }
        return held.min().at();
    }

    /**
     * Values of the element inside {@code run}: each place a relation turns at that is a value, and
     * up to {@code each} different values from every run between two of them and past the last.
     *
     * <p>Where relations part the run, nearest the place each part is bounded by, which is the value
     * beside the line an author would write ({@link #walked}). Where none does, the run is the
     * values an element may hold and there is no line to be beside: the values standing for it are
     * the ones near where the values are usually near ({@link #standingIn}).
     *
     * <p>Where a relation turns is a number and not always a value: {@code 3 * x > 1} turns at a
     * third, which no element is. The run is parted at the exact places it turns at inside it, and
     * at none outside it, so each part is exactly the values that answer every relation one way.
     * Only then is a part written as decimals ({@link #inward}), and only inward, so no value is
     * dropped from a part and none from beside it is let in. A place a value can be is a value
     * besides.
     *
     * @param usual where the values are usually near, which a run no relation parts stands near
     *              and a part left open on the side it is entered from is walked from
     */
    static List<Place> valuesAlong(Carrier carrier, NumericDomain.Bounds run,
                                   List<ExactRatio> turns, int each, UsualPlace usual,
                                   Set<CompositionCapacity> unheld,
                                   Set<CompositionRepertoire> unnamed) {
        if (turns.isEmpty()) {
            return standingIn(carrier, run.min(), run.max(), each, usual, unnamed);
        }
        ExactEnd low = ExactEnd.of(run.min());
        ExactEnd high = ExactEnd.of(run.max());
        List<ExactRatio> inside = turns.stream().distinct().sorted()
                .filter(turn -> (low == null || low.leavesAbove(turn))
                        && (high == null || high.leavesBelow(turn)))
                .toList();
        List<Place> out = new ArrayList<>();
        ExactEnd from = low;
        for (int i = 0; i <= inside.size(); i++) {
            ExactEnd to = high;
            if (i < inside.size()) {
                switch (Count.written(inside.get(i))) {
                    case ExactAnswer.Held<Optional<Count>>(Optional<Count> written) ->
                            to = new ExactEnd(inside.get(i), false,
                                    written.map(Endpoint::exclusive).orElse(null));
                    // A place the host had no room to write out still parts the run there, as an
                    // end no decimal is known to be; the value it may be is a number not held and
                    // is said.
                    case ExactAnswer.Unheld<Optional<Count>>(UnheldNumber why) -> {
                        to = new ExactEnd(inside.get(i), false, null);
                        unheld.add(new CompositionCapacity(
                                CompositionCapacity.Where.PLACES_AN_ELEMENT_TURNS_AT, why));
                    }
                }
            }
            switch (inward(from, to)) {
                case Part.Between(Endpoint lo, Endpoint hi) ->
                        out.addAll(walked(carrier, lo, hi, each, usual, unnamed));
                case Part.Empty _ -> { }
                // A part this could not write leaves its values unoffered, which is a number not
                // held and is said.
                case Part.NotWorkedOut(UnheldNumber why) -> unheld.add(new CompositionCapacity(
                        CompositionCapacity.Where.PLACES_AN_ELEMENT_TURNS_AT, why));
            }
            if (i < inside.size()) {
                if (to.written() != null) {
                    Place value = carrier.onTheGrid(to.written().at());
                    if (value != null) {
                        out.add(value);
                    }
                }
                from = to;
            }
        }
        return out;
    }

    /**
     * Values of an element inside {@code run}, for an order that is not counted: each place a
     * relation turns at that the run holds, and up to {@code each} different values from every run
     * between two of them and past the last.
     *
     * <p>No arithmetic parts the run here, since there is no distance between two values of the
     * order. A place a relation turns at is a value and the run between two of them is walked from
     * the carrier, which names a value inside it where there is one.
     */
    static List<Place> valuesAlongAnOrder(Carrier carrier, NumericDomain.Bounds run,
                                          List<Place> turns, int each, OfTheType element,
                                          Set<CompositionRepertoire> unnamed) {
        List<Place> inside = new ArrayList<>();
        for (Place turn : turns) {
            if (holds(run, turn) && inside.stream().noneMatch(turn::sameAs)) {
                inside.add(turn);
            }
        }
        inside.sort(Place::compareTo);
        List<Place> out = new ArrayList<>();
        Endpoint from = run.min();
        for (Place turn : inside) {
            out.addAll(admitted(carrier, from, Endpoint.exclusive(turn), each, element, unnamed));
            // A place the type refuses still parts the run, and is no value to offer.
            if (element.admits(turn)) {
                out.add(turn);
            }
            from = Endpoint.exclusive(turn);
        }
        out.addAll(admitted(carrier, from, run.max(), each, element, unnamed));
        return out;
    }

    /**
     * Up to {@code each} values of {@code element} from {@code low} to {@code high} along an order
     * that is not counted: those the order names there that the type admits, then, short of that
     * many, ones the type admits there. A part the order names nothing in is said only where
     * nothing is offered in it.
     */
    private static List<Place> admitted(Carrier carrier, Endpoint low, Endpoint high, int each,
                                        OfTheType element, Set<CompositionRepertoire> unnamed) {
        Set<CompositionRepertoire> named = EnumSet.noneOf(CompositionRepertoire.class);
        // An order that does not count, which a string's is: no place on it is usually near.
        List<Place> out = new ArrayList<>(walked(carrier, low, high, each, UsualPlace.NONE, named)
                .stream()
                .filter(element::admits).toList());
        if (out.size() < each) {
            for (Place more : element.inside(low, high, each)) {
                if (out.size() < each && out.stream().noneMatch(more::sameAs)) {
                    out.add(more);
                }
            }
        }
        if (out.isEmpty()) {
            unnamed.addAll(named);
        }
        return out;
    }

    /** Whether {@code run} holds {@code place}. */
    private static boolean holds(NumericDomain.Bounds run, Place place) {
        Endpoint low = run.min();
        Endpoint high = run.max();
        if (low != null) {
            int compared = low.at().compareTo(place);
            if (compared > 0 || (compared == 0 && !low.inclusive())) {
                return false;
            }
        }
        if (high != null) {
            int compared = high.at().compareTo(place);
            if (compared < 0 || (compared == 0 && !high.inclusive())) {
                return false;
            }
        }
        return true;
    }

    /**
     * One end of a part of a run, at the exact number it is; a missing end is none.
     *
     * @param at        where the part ends
     * @param inclusive whether a value at {@code at} is in the part
     * @param written   the end as a decimal, where one is {@code at}; null where none is
     */
    private record ExactEnd(ExactRatio at, boolean inclusive, Endpoint written) {

        static ExactEnd of(Endpoint end) {
            return end == null ? null
                    : new ExactEnd(Count.number(end.at()).exactly(), end.inclusive(), end);
        }

        /** Whether this, as a lower end, leaves {@code turn} inside. */
        boolean leavesAbove(ExactRatio turn) {
            int compared = at.compareTo(turn);
            return compared < 0 || (compared == 0 && inclusive);
        }

        /** Whether this, as an upper end, leaves {@code turn} inside. */
        boolean leavesBelow(ExactRatio turn) {
            int compared = at.compareTo(turn);
            return compared > 0 || (compared == 0 && inclusive);
        }
    }

    /** A part of a run between two exact ends, as the decimals it is walked between. */
    private sealed interface Part {

        /** Walked between these; either may be missing. */
        record Between(Endpoint low, Endpoint high) implements Part {}

        /** Nothing is between the ends. */
        record Empty() implements Part {}

        /** The ends could not be written, for this. */
        record NotWorkedOut(UnheldNumber why) implements Part {}
    }

    /**
     * The part between {@code low} and {@code high}, with each end that no decimal is moved inward
     * to the nearest decimal at as many places as the part is narrow, and held there.
     *
     * <p>An end that is a decimal stays where it is, as open or closed as it was, and a part whose
     * ends both are is walked between them with no arithmetic at all — however few places apart
     * they stand. Only an end no decimal is asks how wide the part is: as many places as the width
     * stands above ten to the minus of ({@link ExactRatio#placesItStandsAbove}), so one step of the
     * last place is less than the part is wide, a decimal stands in it, and every decimal between
     * the moved ends is one of the part's. That count is read off the width's order, and the end is
     * rounded by {@link ExactRatio#asDecimal}; neither forms a number as large as the count says.
     */
    private static Part inward(ExactEnd low, ExactEnd high) {
        boolean lowWritten = low == null || low.written() != null;
        boolean highWritten = high == null || high.written() != null;
        if (lowWritten && highWritten) {
            return new Part.Between(low == null ? null : low.written(),
                    high == null ? null : high.written());
        }
        int places = 1;
        if (low != null && high != null) {
            switch (high.at().minus(low.at())) {
                case ExactAnswer.Held<ExactRatio>(ExactRatio width) -> {
                    // One end is no decimal, so the part holds a single place only where that end
                    // is closed, and no end that no decimal is ever is.
                    if (width.signum() <= 0) {
                        return new Part.Empty();
                    }
                    OptionalInt standsAbove = width.placesItStandsAbove();
                    if (standsAbove.isEmpty()) {
                        return new Part.NotWorkedOut(UnheldNumber.MORE_ROOM_COULD_ANSWER);
                    }
                    places = standsAbove.getAsInt();
                }
                case ExactAnswer.Unheld<ExactRatio>(UnheldNumber why) -> {
                    return new Part.NotWorkedOut(why);
                }
            }
        }
        ExactAnswer<Endpoint> lo = lowWritten ? null : roundedIn(low, places, RoundingMode.CEILING);
        ExactAnswer<Endpoint> hi = highWritten ? null : roundedIn(high, places, RoundingMode.FLOOR);
        for (ExactAnswer<Endpoint> end : Arrays.asList(lo, hi)) {
            if (end instanceof ExactAnswer.Unheld<Endpoint>(UnheldNumber why)) {
                return new Part.NotWorkedOut(why);
            }
        }
        return new Part.Between(lo == null ? (low == null ? null : low.written()) : lo.orNull(),
                hi == null ? (high == null ? null : high.written()) : hi.orNull());
    }

    /** {@code end}, which no decimal is known to be, as the decimal at {@code places} on the side of
     *  it {@code towards} says — inside the part, and so held, unless that decimal is the end
     *  itself, which is then as open or closed as the end. */
    private static ExactAnswer<Endpoint> roundedIn(ExactEnd end, int places, RoundingMode towards) {
        return end.at().asDecimal(towards, places).map(at -> {
            Count count = Count.of(at);
            return count.exactly().compareTo(end.at()) == 0
                    ? new Endpoint(count, end.inclusive()) : Endpoint.inclusive(count);
        });
    }

    /**
     * Up to {@code each} different values of a part of a run between two places a relation turns
     * at, from the end there is: the value beside the line an author would write
     * ({@link Carrier#somethingInside}).
     *
     * <p>Or from where the value is usually near, where the side the part is entered from is one
     * nobody drew: the dates of a part open below are today's and those either side of it, above
     * before below, as every outward walk here takes them. Walked one way only from there, a part
     * whose far end is before today would give up today's nearest date and nothing else.
     *
     * <p>A run that holds a value and of which the carrier named none is put in {@code unnamed}:
     * a string above every string a rule wrote is there and is not one this invents, and the run
     * left without a value is this compiler's reach and no answer about the model.
     */
    private static List<Place> walked(Carrier carrier, Endpoint low, Endpoint high, int each,
                                      UsualPlace usual, Set<CompositionRepertoire> unnamed) {
        Towards from = low == null && high != null ? Towards.BELOW : Towards.ABOVE;
        Place first = Endpoint.someValueLiesBetween(low, high)
                ? carrier.somethingInside(low, high, from, usual) : null;
        boolean outward = usual instanceof UsualPlace.Near near
                && near.leftOpenAt(from == Towards.ABOVE ? low : high, from == Towards.ABOVE);
        return steppedFrom(first, carrier, low, high, each, from, outward, unnamed);
    }

    /**
     * Up to {@code each} different values standing for a run no relation parts, which no end of it
     * is asked for ({@link Carrier#aPlaceInside}): where the value is usually near, where the run is
     * left open on either side, and the values either side of it — and otherwise from the run's
     * end, as {@link #walked} takes them.
     *
     * <p>The other question from the one a part beside a line asks. A run of the values an element
     * may hold, bounded only by what its type admits, has no line to be beside: a set of dates from
     * the year 2000 on is today and the days either side of it, as a single such date is today
     * ({@link Partitions}), and not the first of January 2000 and the days after it.
     */
    private static List<Place> standingIn(Carrier carrier, Endpoint low, Endpoint high, int each,
                                          UsualPlace usual, Set<CompositionRepertoire> unnamed) {
        Towards from = low == null && high != null ? Towards.BELOW : Towards.ABOVE;
        Place first = Endpoint.someValueLiesBetween(low, high)
                ? carrier.aPlaceInside(low, high, usual) : null;
        boolean outward = usual instanceof UsualPlace.Near near && near.leftOpenIn(low, high);
        return steppedFrom(first, carrier, low, high, each, from, outward, unnamed);
    }

    /**
     * {@code first} and the values after it, up to {@code each} of them: stepping away from the end
     * {@code from} names, or outward from {@code first} on both sides, the one above before the one
     * below, where {@code outward}.
     */
    private static List<Place> steppedFrom(Place first, Carrier carrier, Endpoint low,
                                           Endpoint high, int each, Towards from, boolean outward,
                                           Set<CompositionRepertoire> unnamed) {
        List<Place> out = new ArrayList<>();
        if (first == null) {
            if (Endpoint.someValueLiesBetween(low, high)) {
                unnamed.add(CompositionRepertoire.PLACES_IN_A_RUN_THAT_ARE_NAMED);
            }
            return out;
        }
        out.add(first);
        // Each side carried from the last place it reached: above it entered from below, below it
        // from above, so each next value is the one beside the last on its side.
        Endpoint lo = Endpoint.exclusive(first);
        Endpoint hi = Endpoint.exclusive(first);
        boolean aboveLeft = outward || from == Towards.ABOVE;
        boolean belowLeft = outward || from == Towards.BELOW;
        while (out.size() < each && (aboveLeft || belowLeft)) {
            if (aboveLeft) {
                Place next = Endpoint.someValueLiesBetween(lo, high)
                        ? carrier.somethingInside(lo, high, Towards.ABOVE, UsualPlace.NONE) : null;
                if (next == null || out.stream().anyMatch(next::sameAs)) {
                    aboveLeft = false;
                } else {
                    out.add(next);
                    lo = Endpoint.exclusive(next);
                }
            }
            if (belowLeft && out.size() < each) {
                Place next = Endpoint.someValueLiesBetween(low, hi)
                        ? carrier.somethingInside(low, hi, Towards.BELOW, UsualPlace.NONE) : null;
                if (next == null || out.stream().anyMatch(next::sameAs)) {
                    belowLeft = false;
                } else {
                    out.add(next);
                    hi = Endpoint.exclusive(next);
                }
            }
        }
        return out;
    }

    /**
     * What is shared out, grouped by what each comes to of every count, in the order they were
     * named: elements, each one element and one or none of each count, or the elements holding
     * one value together ({@link HeldUnder}), each as many elements as it holds and as many of
     * each count as a row holding it alone has.
     *
     * @param counts  each group's part of every count, one per count
     * @param weights how many elements each of a group's values is
     * @param values  each group's values
     * @param unread  what kept a value out of every group, where something did
     */
    private record Groups<V>(List<int[]> counts, List<Integer> weights, List<List<V>> values,
                             Set<ReadingGap> unread) {

        static <V> Groups<V> none() {
            return new Groups<>(new ArrayList<>(), new ArrayList<>(), new ArrayList<>(),
                    new LinkedHashSet<>());
        }

        static Groups<Place> of(List<Asked> asked, TermPath container,
                                Element element, Map<TermPath, ObservedValue> written,
                                List<Place> values) {
            Groups<Place> out = none();
            for (Place value : values) {
                AnElementRead read = new AnElementRead(container, element.term().subjectPath(),
                        written, List.of(element.carrier().valueOf(value)));
                BorderQuantity.Observation one = read.elements().getFirst();
                out.add(value, i -> asked.get(i).at(value, one), asked.size());
            }
            return out;
        }

        /**
         * {@code value}, one element, put in the group of values answering every statement the
         * way it does — the {@code i}-th as {@code answering} says — or in none where some
         * statement could not be read at it.
         */
        void add(V value, IntFunction<AStatementAtARow.Answer> answering, int statements) {
            int[] answer = new int[statements];
            for (int i = 0; i < statements; i++) {
                switch (answering.apply(i)) {
                    case AStatementAtARow.Answer.Holds _ -> answer[i] = 1;
                    case AStatementAtARow.Answer.Fails _ -> answer[i] = 0;
                    case AStatementAtARow.Answer.CouldNotTell(var why) -> {
                        unread.addAll(why);
                        return;
                    }
                }
            }
            add(value, 1, answer);
        }

        /** {@code value}, {@code weight} elements, put in the group of those coming to
         *  {@code counted} of every count. */
        void add(V value, int weight, int[] counted) {
            for (int at = 0; at < counts.size(); at++) {
                if (weights.get(at) == weight && Arrays.equals(counts.get(at), counted)) {
                    values.get(at).add(value);
                    return;
                }
            }
            counts.add(counted);
            weights.add(weight);
            values.add(new ArrayList<>(List.of(value)));
        }

        /**
         * These without the groups a count asking that no element meet its statement rules out:
         * a container holding one of their values meets no sharing, so none is looked at.
         */
        Groups<V> keptBy(List<Asked> asked) {
            Groups<V> kept = new Groups<>(new ArrayList<>(), new ArrayList<>(),
                    new ArrayList<>(), unread);
            groups:
            for (int g = 0; g < counts.size(); g++) {
                for (int i = 0; i < asked.size(); i++) {
                    if (counts.get(g)[i] > 0 && noneMayMeet(asked.get(i))) {
                        continue groups;
                    }
                }
                kept.counts.add(counts.get(g));
                kept.weights.add(weights.get(g));
                kept.values.add(values.get(g));
            }
            return kept;
        }

        /** Whether {@code asked} leaves no count of elements meeting it above none, as far as a
         *  container is composed. */
        private static boolean noneMayMeet(Asked asked) {
            for (int meeting = 1; meeting <= MOST_ELEMENTS; meeting++) {
                if (asked.asMany(meeting)) {
                    return false;
                }
            }
            return true;
        }

        /** The values a share draws: so many from each group, the first value again and again
         *  where a value may repeat and that many different ones where it may not. */
        List<V> drawn(int[] share, boolean distinct) {
            List<V> out = new ArrayList<>();
            for (int g = 0; g < share.length; g++) {
                for (int n = 0; n < share[g]; n++) {
                    out.add(values.get(g).get(distinct ? n : 0));
                }
            }
            return out;
        }

        String unreadSaid() {
            return "an element a statement could not be read at was not chosen: " + unread;
        }
    }

    /**
     * Every way of sharing a size out among the groups that meets every count, in the order the
     * groups were found and with the first group's share largest first.
     */
    private static final class Sharing {

        private final Groups<?> groups;
        private final List<Asked> asked;
        private final List<Together> together;
        private final NumericSet size;
        /** How many of a group's values one sharing may draw, by the group. */
        private final IntUnaryOperator capacity;

        /** How many more sharings this may look at, over every size it is asked for. */
        private int left;

        /** Whether a sharing was in front of the walk when there was no room left for it. */
        private boolean stopped;

        /** Whether some group from the {@code g}-th on meets the {@code i}-th thing asked, at
         *  {@code [g][i]}: worked out once, from the last group back. */
        private final boolean[][] meetableFrom;

        /** How many more elements may yet meet each thing asked, filled in where a sharing is
         *  asked whether it can still come to what is asked. */
        private final int[] more;

        /** No more elements, which is what a sharing whose every element is shared out has. */
        private final int[] none;

        /** How many of the elements of the sharing handed over last meet each thing asked. */
        private int[] handedOver;

        /**
         * Sharings of the elements among {@code groups} that meet everything {@code asked}, and
         * that leave each of {@code together} a way of holding.
         *
         * <p>A value of a group is as many elements as the group weighs, and adds the group's
         * part of each count; no part is more than the elements it is, so every element left
         * adds at most one to a count.
         *
         * @param capacity how many of a group's values one sharing may draw, by the group
         * @param most     how many sharings this looks at, over every size it is asked for
         */
        Sharing(Groups<?> groups, List<Asked> asked, List<Together> together, NumericSet size,
                IntUnaryOperator capacity, int most) {
            this.groups = groups;
            this.asked = asked;
            this.together = together;
            this.size = size;
            this.capacity = capacity;
            this.left = most;
            int count = groups.counts().size();
            this.meetableFrom = new boolean[count + 1][asked.size()];
            for (int g = count - 1; g >= 0; g--) {
                int[] counted = groups.counts().get(g);
                for (int i = 0; i < asked.size(); i++) {
                    meetableFrom[g][i] = counted[i] > 0 || meetableFrom[g + 1][i];
                }
            }
            this.more = new int[asked.size()];
            this.none = new int[asked.size()];
        }

        /**
         * Hands each sharing of {@code elements} that meets every count to {@code take}, in order,
         * until {@code take} answers that it has enough or the sharings this may look at are
         * spent.
         *
         * @return whether every sharing of that size was looked at
         */
        boolean each(int elements, Predicate<int[]> take) {
            if (size != null && !size.holds(Count.of(elements), Carrier.WHOLE)) {
                return true;
            }
            return share(new int[groups.counts().size()], new int[asked.size()], 0, elements,
                    take);
        }

        /** Whether a sharing was left unlooked at for the figure, which is what the walk was
         *  stopped by and not the sharings running out. */
        boolean spent() {
            return stopped;
        }

        /**
         * @param meeting how many of the elements shared out before {@code g} meet each statement
         */
        private boolean share(int[] share, int[] meeting, int g, int remaining,
                              Predicate<int[]> take) {
            if (g == share.length) {
                if (remaining != 0) {
                    return true;
                }
                if (left == 0) {
                    stopped = true;
                    return false;
                }
                left--;
                if (!meetsEveryCount(meeting)) {
                    return true;
                }
                handedOver = meeting;
                return take.test(share.clone());
            }
            // A sharing whose counts the elements left cannot bring to what is asked, or have
            // already taken past it, is none whatever the rest of it is, and is not walked.
            if (!stillMeetable(meeting, g, remaining)) {
                return true;
            }
            int weight = groups.weights().get(g);
            int most = Math.min(remaining / weight, capacity.applyAsInt(g));
            int[] counted = groups.counts().get(g);
            for (int n = most; n >= 0; n--) {
                share[g] = n;
                for (int i = 0; i < counted.length; i++) {
                    meeting[i] += n * counted[i];
                }
                boolean more = share(share, meeting, g + 1, remaining - n * weight, take);
                for (int i = 0; i < counted.length; i++) {
                    meeting[i] -= n * counted[i];
                }
                if (!more) {
                    share[g] = 0;
                    return false;
                }
            }
            share[g] = 0;
            return true;
        }

        /**
         * Whether every count can still come to what it asks, with {@code meeting} elements of the
         * groups before {@code from} meeting each statement and {@code remaining} elements still to
         * share out among the rest: somewhere between what it has and what it would have were every
         * element left one meeting it.
         */
        private boolean stillMeetable(int[] meeting, int from, int remaining) {
            for (int i = 0; i < asked.size(); i++) {
                more[i] = meetableFrom[from][i] ? remaining : 0;
                int most = meeting[i] + more[i];
                boolean some = false;
                for (int count = meeting[i]; count <= most && !some; count++) {
                    some = asked.get(i).asMany(count);
                }
                if (!some) {
                    return false;
                }
            }
            return leavesAWay(meeting, more);
        }

        /**
         * Whether every statement of the elements together still has a way of holding, with
         * {@code meeting} elements meeting each thing asked and up to {@code more} besides.
         */
        private boolean leavesAWay(int[] meeting, int[] more) {
            for (Together each : together) {
                if (each.counting().at(meeting, more) == AStatementAtARow.Counting.FAILS) {
                    return false;
                }
            }
            return true;
        }

        /** Whether a sharing every element of which is shared out, {@code meeting} of them
         *  meeting each thing asked, meets every count and leaves every statement a way. */
        private boolean meetsEveryCount(int[] meeting) {
            for (int i = 0; i < asked.size(); i++) {
                if (!asked.get(i).asMany(meeting[i])) {
                    return false;
                }
            }
            return leavesAWay(meeting, none);
        }

        /**
         * Whether every statement of the elements together holds of the sharing handed over last,
         * by how many of its elements meet each thing asked, whatever else the elements are — so
         * a container of it need not be read for them. Asked while the sharing is in hand.
         */
        boolean holdsTogether() {
            for (Together each : together) {
                if (each.counting().at(handedOver, none) != AStatementAtARow.Counting.HOLDS) {
                    return false;
                }
            }
            return true;
        }
    }

    /**
     * Whether a container of {@code values}, read as a row's container is, has as many elements
     * meeting each statement as its count asks — every count the reading leaves it, where an
     * element could not be read.
     */
    private static boolean readsAsAsked(List<Asked> asked, TermPath container,
                                        Element element, Map<TermPath, ObservedValue> written,
                                        List<Place> values) {
        List<ObservedValue> observed = new ArrayList<>();
        for (Place each : values) {
            observed.add(element.carrier().valueOf(each));
        }
        AnElementRead whole = new AnElementRead(container, element.term().subjectPath(), written,
                observed);
        for (Asked each : asked) {
            if (!(each.over(container, values, whole) instanceof AStatementAtARow.Answer.Holds)) {
                return false;
            }
        }
        return true;
    }

    /** The container holding an element for each value, under the names both wear. */
    private static FixtureTemplate holdingThese(List<Place> values, Carrier carrier, TypeView view,
                                                TypeView ofTheElement,
                                                RuleReadingSource ruleSource) {
        List<FixtureTemplate> elements = new ArrayList<>();
        for (Place each : values) {
            FixtureTemplate one = WornNames.under(ofTheElement.wrappers(),
                    FixtureTemplate.on(carrier, each, ruleSource.symbols().scope()::reach),
                    ruleSource);
            if (one == null) {
                return null;
            }
            elements.add(one);
        }
        return WornNames.under(view.wrappers(), FixtureTemplate.collection(elements), ruleSource);
    }

    /**
     * A row holding nothing but a container of these elements and the numbers beside them, read
     * the way a row is.
     *
     * <p>Each element is a reading of its own ({@link #elements}), and the container is walked
     * through them. Anything else the statements ask for — a position this does not hold, the
     * elements of another container — could not be walked, which a statement reads as not being
     * able to tell and never as failing.
     */
    record AnElementRead(TermPath container, TermPath element,
                                 Map<TermPath, ObservedValue> written,
                                 List<ObservedValue> held) implements BorderQuantity.Observation {

        /** Each element, read as this row with that element chosen. */
        List<BorderQuantity.Observation> elements() {
            List<BorderQuantity.Observation> out = new ArrayList<>();
            for (ObservedValue each : held) {
                out.add(new AnElementRead(container, element, written, List.of(each)));
            }
            return out;
        }

        @Override
        public WalkResult<ObservationAtPoint> at(TermPath path) {
            if (path.equals(element)) {
                return held.size() == 1
                        ? WalkResult.reached(new ObservationAtPoint.Value(held.getFirst()))
                        : WalkResult.couldNotWalk();
            }
            ObservedValue value = written.get(path);
            return value == null ? WalkResult.couldNotWalk()
                    : WalkResult.reached(new ObservationAtPoint.Value(value));
        }

        @Override
        public WalkResult<List<ObservedValue>> everyValueAt(TermPath path) {
            return path.equals(element) ? WalkResult.reached(held) : WalkResult.couldNotWalk();
        }

        @Override
        public WalkResult<List<BorderQuantity.Observation>> eachElementOf(TermPath of) {
            return of.equals(container) ? WalkResult.reached(elements())
                    : WalkResult.couldNotWalk();
        }
    }

    private static TermRealizations.Realization none(String why) {
        return new TermRealizations.Realization.None(
                Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE, why);
    }

    /** Elements of a kind nothing here chooses, which is the population and no proof. */
    private static TermRealizations.Realization notChosen(String why) {
        return new TermRealizations.Realization.Unexhausted(CompositionShortfall.writing(
                Set.of(CompositionRepertoire.ELEMENTS_CHOSEN_FOR_A_COUNT)), why);
    }

    private CardinalityComposer() {}
}
