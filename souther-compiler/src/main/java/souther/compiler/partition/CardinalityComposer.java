package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.diag.msg.SearchMessage;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.Shape;
import souther.compiler.check.TypeView;
import souther.compiler.inputs.ElementProjection;
import souther.compiler.inputs.ElementValue;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Spelling;
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
     * Containers of {@code sourceType}, written at {@code container}, meeting every one of
     * {@code counts} at the set {@code demands} asks it for, with some element standing in the set
     * asked of each of {@code standingAt}, coming to one of the numbers asked of each of
     * {@code totals}, and holding as many elements as {@code manyItHolds} is asked for where it is
     * not null.
     *
     * @param together   statements the elements are to meet together, each one of several ways the
     *                   elements may take — which every container composed here meets
     * @param standingAt the element itself, each asked to stand in a set: a value the row places at
     *                   an element, which some element of the container is
     * @param totals     what the container is asked to come to, each with the numbers tried for it
     * @param measuring  the orders the input's numbers are counted on, which a number inside an
     *                   element chosen among its values is read at
     * @param within     the region with every number of the row a count's statement reads beside
     *                   an element standing at one value
     */
    static TermRealizations.Realization compose(Type sourceType, List<List<String>> keptApart,
                                                TermPath container,
                                                List<RealizationTarget.ACount> counts,
                                                List<RealizationTarget.ElementsMeetingTogether>
                                                        together,
                                                SequencedMap<RealizationTarget, AskedAt> demands,
                                                RealizationTarget.OfANumber manyItHolds,
                                                List<RealizationTarget.OfANumber> standingAt,
                                                List<ContainerAsAWhole.ATotal> totals,
                                                Quantities measuring, SearchRegion within,
                                                RuleReadingContext reading) {
        RuleReadingSource ruleSource = reading.source();
        List<Asked> asked = new ArrayList<>();
        // Each count as the counts it is asked for, and not as the one a row was named at: the
        // item and every condition on the way that ask for it leave a region, and which count of
        // it the container holds is chosen here.
        for (RealizationTarget.ACount each : counts) {
            AskedAt at = demands.get(each);
            if (at == null) {
                return none(new SearchMessage.NothingSaysHowManyElementsMeet(
                        String.valueOf(container), String.valueOf(each)));
            }
            asked.add(new Asked.SoManyMeeting(each.count().perElement(), at.about().values(),
                    each.count().differentAt(), each.count().across()));
        }
        // Where a count is of the different values the elements meeting a statement hold, every
        // element is chosen apart from the others at that place: then each counts once, and the
        // sharings, which count elements, count the values.
        Quantity.TheValue apartAt = null;
        for (RealizationTarget.ACount each : counts) {
            Quantity.TheValue at = each.count().differentAt().orElse(null);
            if (at != null && apartAt != null && !apartAt.equals(at)) {
                return notChosen(new SearchMessage.TheValuesAreCountedAtTwoPlaces(
                        String.valueOf(container), String.valueOf(apartAt), String.valueOf(at)));
            }
            apartAt = at != null ? at : apartAt;
        }
        NumericSet size = null;
        if (manyItHolds != null) {
            AskedAt holds = demands.get(manyItHolds);
            if (holds == null || holds.walking() == null) {
                return none(new SearchMessage.NothingSaysHowManyElementsItHolds(
                        String.valueOf(container)));
            }
            size = holds.walking();
        }
        Optional<TermPath> across = counts.isEmpty() ? Optional.empty()
                : counts.getFirst().count().across();
        if (counts.stream().anyMatch(each -> !each.count().across().equals(across))) {
            return notChosen(new SearchMessage.CountedInOneAndAcrossAll(String.valueOf(container)));
        }
        if (across.isPresent()) {
            if (!totals.isEmpty()) {
                return notChosen(new SearchMessage.CountedAcrossTheContainersHoldingThem(
                        String.valueOf(container)));
            }
            return composeAcross(asked, standingAt, demands, container, across.get(), size,
                    together, sourceType, keptApart, apartAt, measuring, within, reading);
        }
        TypeView view = TypeView.of(sourceType, ruleSource.inners(), ruleSource.symbols(),
                ruleSource.kinds(), ruleSource.sums());
        if (!(view.shape() instanceof Shape.Sequence holding)
                || !container.element().outermostContainer().equals(container)) {
            return notChosen(new SearchMessage.NoListOrSetWrittenWhereItStands(
                    String.valueOf(container)));
        }
        // A statement the elements meet together is one their values meet, which is what they are
        // chosen among their values for.
        List<AStatementAtARow> stated = new ArrayList<>();
        for (RealizationTarget.ElementsMeetingTogether each : together) {
            stated.add(AStatementAtARow.of(each.stated(), each.behavior(), measuring));
        }
        if (!stated.isEmpty()) {
            return amongItsValues(asked, stated, standingAt, totals, demands, container, size,
                    sourceType, view, holding, keptApart, apartAt, measuring, within, reading,
                    new Standing.WhereItIsWritten(sourceType, reading));
        }
        // What another container is made to hold for the elements chooses none of their values,
        // so none are chosen apart that way.
        if (standingAt.isEmpty() && totals.isEmpty() && apartAt == null && !counts.isEmpty()
                && counts.stream().allMatch(each -> ACountHandedOn.of(each.count()).isPresent())) {
            List<ACountHandedOn> handed = new ArrayList<>();
            List<OptionalInt> meeting = new ArrayList<>();
            for (RealizationTarget.ACount each : counts) {
                handed.add(ACountHandedOn.of(each.count()).orElseThrow());
                meeting.add(ACountHandedOn.counted(demands.get(each)));
            }
            return handingOn(asked, handed, meeting, size, view, keptApart, reading);
        }
        // Every element is chosen among the values it is read at whole, whether it is one number
        // or several, whether or not the different values of a place are counted, and whether or
        // not what it answers reads the container as a whole.
        return amongItsValues(asked, List.of(), standingAt, totals, demands, container, size,
                sourceType, view, holding, keptApart, apartAt, measuring, within, reading,
                new Standing.WhereItIsWritten(sourceType, reading));
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
            Type sourceType, List<List<String>> keptApart, Quantity.TheValue apartAt,
            Quantities measuring, SearchRegion within, RuleReadingContext reading) {
        if (size != null || !together.isEmpty()) {
            return notChosen(new SearchMessage.AskedOfOneOfTheContainers(String.valueOf(container)));
        }
        for (Asked each : asked) {
            if (each instanceof Asked.SoManyMeeting(AStatementAtARow perElement, _, _, _)
                    && !perElement.answersHoweverTheElementsAreSharedOut(container, across)) {
                return notChosen(new SearchMessage.WhatAnElementAnswersReadsAContainerHoldingIt(
                        String.valueOf(container)));
            }
        }
        for (RealizationTarget.OfANumber each : standingAt) {
            if (AStatementAtARow.readsAroundTheElement(each.term(), container, across)) {
                return notChosen(new SearchMessage.ReadOffAContainerHoldingAnElement(
                        String.valueOf(each.term()), String.valueOf(container)));
            }
        }
        RuleReadingSource ruleSource = reading.source();
        NestedContainersAddingUp.Inside inner =
                NestedContainersAddingUp.ofTheContainerAt(sourceType, container, reading);
        if (inner == null || !across.equals(container.element().outermostContainer())) {
            return notChosen(new SearchMessage.NoListOrSetInsideTheElements(
                    String.valueOf(container)));
        }
        TypeView view = TypeView.of(inner.type(), ruleSource.inners(), ruleSource.symbols(),
                ruleSource.kinds(), ruleSource.sums());
        if (!(view.shape() instanceof Shape.Sequence holding)) {
            return notChosen(new SearchMessage.NoListOrSet(String.valueOf(container)));
        }
        return amongItsValues(asked, List.of(), standingAt, List.of(), demands, container, null,
                inner.type(), view, holding, inner.keptApart(), apartAt, measuring, within, reading,
                new Standing.AcrossTheElementsOf(across, container, sourceType, keptApart, within,
                        reading));
    }

    /**
     * Where the elements chosen for a container stand in the input: the row a container of them
     * is read as, and the rows written holding them.
     */
    sealed interface Standing {

        /** {@code holding}, a row holding a container of the elements chosen, as it is read. */
        BorderQuantity.Observation read(BorderQuantity.Observation holding);

        /** At most {@code room} rows holding {@code values}, with what writing them met — or null
         *  where they are written as nothing. */
        TermRealizations.Realization written(List<ObservedValue> values, int room);

        /** The container where it stands, of {@code type}. */
        record WhereItIsWritten(Type type, RuleReadingContext reading) implements Standing {

            @Override
            public BorderQuantity.Observation read(BorderQuantity.Observation holding) {
                return holding;
            }

            /**
             * Written under the type's names, the container itself under none: what is chosen is
             * the elements, and the names go on as every value a row writes wears them.
             */
            @Override
            public TermRealizations.Realization written(List<ObservedValue> values, int room) {
                RuleReadingSource source = reading.source();
                TypeView view = TypeView.of(type, source.inners(), source.symbols(),
                        source.kinds(), source.sums());
                return ObservedFixtures.of(new ObservedValue.Sequence(values),
                        source.inners().terminal(type), reading)
                        instanceof ObservedFixtures.Writing.Written<FixtureTemplate>(
                                FixtureTemplate one)
                        && WornNames.under(view.wrappers(), one, source)
                                instanceof FixtureTemplate named
                        ? new TermRealizations.Realization.Built(List.of(named),
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
            public TermRealizations.Realization written(List<ObservedValue> values, int room) {
                return new NestedContainersAddingUp(container.element()).holdingThe(type,
                        keptApart, values, within, reading, room);
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
                        Set.of()), new SearchMessage.NoCountWalkedIsOneAContainerMeets());
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
        return new TermRealizations.Realization.Unexhausted(rest,
                new SearchMessage.NoSizeHasRoomForTheCount());
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
     * @param totals     what the row asks the container to come to, beside the counts
     *                   ({@link ContainerAsAWhole})
     * @param holding    what the container is, a list or a set
     * @param standing   where the elements chosen stand in the input: how a container of them is
     *                   read, and the rows written holding them
     */
    private static TermRealizations.Realization amongItsValues(List<Asked> counted,
                                                               List<AStatementAtARow> together,
                                                               List<RealizationTarget.OfANumber>
                                                                       standingAt,
                                                               List<ContainerAsAWhole.ATotal>
                                                                       totals,
                                                               SequencedMap<RealizationTarget,
                                                                       AskedAt> demands,
                                                               TermPath container,
                                                               NumericSet size, Type sourceType,
                                                               TypeView view,
                                                               Shape.Sequence holding,
                                                               List<List<String>> keptApart,
                                                               Quantity.TheValue apartAt,
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
                return none(new SearchMessage.NothingSaysWhereItStandsInsideAnElement(
                        String.valueOf(each.term()), String.valueOf(container)));
            }
            asked.add(new Asked.SomeElementAt(each.term().subjectPath(), at.walking(), on));
        }
        // What each statement of the elements together says of one element, once however many of
        // them say it, with no count of it asked: where in what is asked each is.
        List<Together> statements = new ArrayList<>();
        Map<Spelling, Integer> saidOfAnElement = new LinkedHashMap<>();
        for (AStatementAtARow each : together) {
            Map<Spelling, Integer> at = new LinkedHashMap<>();
            each.ofEachElementOf(container).forEach((key, perElement) -> {
                Integer index = saidOfAnElement.get(key);
                if (index == null) {
                    index = asked.size();
                    asked.add(new Asked.SoManyMeeting(perElement, ANY_COUNT, Optional.empty(),
                            Optional.empty()));
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
            });
        }
        // Elements its rules keep apart are chosen among more than one value of each part.
        List<List<String>> apartByItsRules = ElementsKeptApart.at(view, keptApart, reading);
        boolean keptApartByItsRules = !apartByItsRules.isEmpty();
        Set<CompositionCapacity> unheld = new LinkedHashSet<>();
        Set<CompositionRepertoire> unnamed = EnumSet.noneOf(CompositionRepertoire.class);
        Set<CompositionBudget> refused = EnumSet.noneOf(CompositionBudget.class);
        List<FixtureTemplate> built = new ArrayList<>();
        Set<ReadingGap> unread = new LinkedHashSet<>();
        // The numbers the statements read beside an element, each at the one value the row was
        // fixed at, which the row an element is read in holds too ({@link #withNumbersBeside}).
        Map<NumericTerm, Place> outside = settledOutside(asked, container, within);
        // The numbers of the container as a whole the row asks or the statements read, each fixed
        // at one number before an element is chosen: what an element answers reads them.
        ContainerAsAWhole whole = ContainerAsAWhole.of(container, view, asked, totals, outside,
                size, measuring, within, reading);
        if (whole == null) {
            return notChosen(new SearchMessage.ATotalOfAPlaceWhoseNumbersAreNotWhole(
                    String.valueOf(container)));
        }
        // The container of none needs no element and no choice of those numbers — what it comes
        // to is read off it — so it is looked at first and apart from both, and offered where the
        // row and the region leave it, as every container is ({@link ContainerAsAWhole#ofNone}).
        ContainerAsAWhole.Fixed ofNone = whole.ofNone();
        if ((size == null || size.holds(Count.of(0), Carrier.WHOLE)) && ofNone != null
                && ofNone.holding(within, 0).admits(List.of(), List.of(), List.of())) {
            writtenIfAsked(List.of(), standing.read(withNumbersBeside(
                            ElementValues.holding(container, reading, sourceType, List.of()),
                            outside)),
                    asked, container, false, together, standing, built, refused, unnamed, unheld);
        }
        TermRealizations.Together choices = whole.isEmpty()
                ? new TermRealizations.Together(List.of(List.of()), CompositionShortfall.NONE)
                : whole.choices();
        // Whether any choice of the numbers of the whole left an element a value: where none did,
        // the choices not tried are no more than the ones tried, and what stopped them is nothing.
        boolean anElementCanBe = false;
        for (List<Place> chosen : choices.each()) {
            ContainerAsAWhole.Fixed fixed = whole.at(chosen);
            Map<NumericTerm, Place> beside = fixed.beside(outside);
            // Where inside an element the numbers are that values are listed at, which is where
            // an element is asked of the region at ({@link ContainerAsAWhole.Sized#admits}).
            Set<TermPath> listedAt = new LinkedHashSet<>();
            // Where the different values at a place are counted, the values that place is chosen
            // at are as many as a container has elements, and the elements are listed holding one
            // of them there at a time: which value a group is under is apart from what it holds
            // ({@link UnderEachValue}), and listed against every value of the other parts, those
            // values would fill the listing in place of the others'.
            BiFunction<TermPath, TypeView, List<ObservedValue>> numbers = (at, part) -> {
                listedAt.add(at);
                return numbersAt(at, OfTheType.of(part, reading), asked, apartAt, measuring,
                        within, beside, keptApartByItsRules ? MOST_ELEMENTS : 1, unheld, unnamed,
                        reading.today());
            };
            ListedByValue byValue = listedByValue(container, holding.element(), reading, apartAt,
                    numbers, (at, part) -> {
                        listedAt.add(at);
                        return numbersAt(at, OfTheType.manyOf(part, reading), asked, apartAt,
                                measuring, within, beside, MOST_ELEMENTS, unheld, unnamed,
                                reading.today());
                    });
            List<TermPath> parts = List.copyOf(listedAt);
            if (byValue == null || (apartAt != null && byValue.values().isEmpty())) {
                if (whole.isEmpty() && built.isEmpty()) {
                    return byValue == null
                            ? notChosen(new SearchMessage.APartNeitherOneOfSoManyNorNumbers(
                                    String.valueOf(container)))
                            : notChosen(new SearchMessage.TheDifferentValuesAreCounted(
                                    String.valueOf(apartAt), String.valueOf(container)));
                }
                unnamed.add(CompositionRepertoire.ELEMENTS_CHOSEN_FOR_A_COUNT);
                continue;
            }
            ElementValues ofTheElement = byValue.first();
            ValuesOfAnElement.Listed listed = ofTheElement.listed();
            if (!listed.all()) {
                refused.add(CompositionBudget.VALUES_AN_ELEMENT_IS_CHOSEN_AMONG);
            }
            anElementCanBe |= !listed.values().isEmpty();
            Function<List<ObservedValue>, BorderQuantity.Observation> holdingThem =
                    values -> standing.read(withNumbersBeside(
                            ofTheElement.holding(sourceType, values), outside));
            // What a group of elements answers is read with the numbers of the whole standing
            // where they are fixed ({@link ContainerAsAWhole.Fixed#beside}): what it answers in
            // any container coming to them, and not what the group alone comes to.
            Function<List<ObservedValue>, BorderQuantity.Observation> readingOf =
                    group -> standing.read(withNumbersBeside(
                            ofTheElement.holding(sourceType, group), beside));
            // Where the different values at a place are counted, what is shared out is the
            // elements holding one value there together, each group with a value of its own: how
            // many values a count has is how many such groups it has, whatever each holds.
            // Elsewhere, each element on its own.
            Groups<?> groups;
            IntUnaryOperator capacity;
            Function<int[], List<ObservedValue>> drawing;
            // The values each element drawn answers alike to, which it may be moved from to come
            // to a total: the group's, where an element is drawn from a group of its own and may
            // repeat a value.
            Function<int[], List<List<ObservedValue>>> alikeTo = share -> null;
            if (apartAt == null) {
                Groups<ObservedValue> every = Groups.none();
                for (ObservedValue value : listed.values()) {
                    BorderQuantity.Observation row = readingOf.apply(List.of(value));
                    every.add(value, i -> ofAnElement.get(i).apply(row), asked.size());
                }
                Groups<ObservedValue> kept = every.keptBy(asked);
                groups = kept;
                capacity = g -> keptApartByItsRules ? kept.values().get(g).size()
                        : Integer.MAX_VALUE;
                drawing = share -> kept.drawn(share, keptApartByItsRules);
                if (!keptApartByItsRules) {
                    alikeTo = share -> {
                        List<List<ObservedValue>> out = new ArrayList<>();
                        for (int g = 0; g < share.length; g++) {
                            for (int n = 0; n < share[g]; n++) {
                                out.add(kept.values().get(g));
                            }
                        }
                        return out;
                    };
                }
            } else {
                UnderEachValue under = UnderEachValue.of(byValue.values().size(), byValue.under(),
                        readingOf, container, apartAt, asked, keptApartByItsRules,
                        UnderEachValue.oneEachUnder(container, apartAt, apartByItsRules), refused);
                groups = under.groups();
                capacity = under::capacity;
                drawing = under::drawn;
            }
            unread.addAll(groups.unread());
            Sharing sharing = new Sharing(groups, asked, statements, size, capacity, MOST_SHARES);
            Function<int[], List<List<ObservedValue>>> alike = alikeTo;
            boolean stopped = false;
            // From one: the container of none was looked at before any choice.
            for (int elements = 1; ; elements++) {
                // Past the most a container is composed with there are more sizes, which leave
                // something untried only where an element can be at all.
                if (elements > MOST_ELEMENTS) {
                    if (!listed.values().isEmpty()) {
                        refused.add(CompositionBudget.ELEMENTS_A_COUNT_IS_COMPOSED_WITH);
                    }
                    break;
                }
                // Nor where the totals fixed ask two things of one place for so many elements, or
                // the region leaves so many nothing coming to them: no elements meet both, which
                // is said before any is drawn.
                if ((fixed.many() != null && elements != fixed.many())
                        || !fixed.comesTogetherIn(elements)) {
                    continue;
                }
                ContainerAsAWhole.Sized sized = fixed.holding(within, elements);
                if (!sized.leavesSomething()) {
                    continue;
                }
                boolean walkedThem = sharing.each(elements, share -> {
                    // At or past it: one choice of the elements may be written as several rows.
                    if (built.size() >= MOST_OFFERED) {
                        return false;
                    }
                    List<ObservedValue> drawn = drawing.apply(share);
                    if (drawn == null) {
                        return true;
                    }
                    // And moved to come to every total fixed, inside the runs they answer over,
                    // from each start they answer alike to: the values of a group are alike to
                    // the statements and not to everything the region knows of them, so a
                    // container from each start an element tries first is asked of the region,
                    // and offered where it leaves it.
                    List<List<ObservedValue>> starts =
                            fixed.movesTheElements() ? alike.apply(share) : null;
                    int ways = 1;
                    for (List<ObservedValue> each : starts == null ? List.<List<ObservedValue>>of()
                            : starts) {
                        ways = Math.max(ways, each.size());
                    }
                    Set<List<ObservedValue>> offered = new HashSet<>();
                    boolean turnedAway = false;
                    int variant = 0;
                    for (; variant < Math.min(ways, MOST_OFFERED)
                            && built.size() < MOST_OFFERED; variant++) {
                        List<ObservedValue> values = !fixed.movesTheElements() ? drawn
                                : sized.spread(drawn, starts, variant,
                                        place -> turnsOf(place, asked, beside), parts,
                                        apartByItsRules, refused, unnamed);
                        if (values == null || !offered.add(values)) {
                            continue;
                        }
                        if (sized.admits(values, parts, apartByItsRules)) {
                            writtenIfAsked(values, holdingThem.apply(values), asked, container,
                                    sharing.holdsTogether(), together, standing, built, refused,
                                    unnamed, unheld);
                        } else {
                            turnedAway = true;
                        }
                    }
                    // A container the region turned away from one start, where some starts were
                    // never tried first, is one of the ways not walked.
                    if (turnedAway && variant < ways) {
                        unnamed.add(CompositionRepertoire.ELEMENTS_CHOSEN_FOR_A_COUNT);
                    }
                    return true;
                });
                if (!walkedThem) {
                    refused.add(sharing.spent() ? CompositionBudget.SHARES_A_COUNT_IS_TRIED_AT
                            : CompositionBudget.CONTAINERS_A_COUNT_IS_OFFERED);
                    stopped = true;
                    break;
                }
            }
            if (stopped) {
                break;
            }
        }
        if (!unread.isEmpty()) {
            unnamed.add(CompositionRepertoire.ELEMENTS_CHOSEN_FOR_A_COUNT);
        }
        // Where no choice was tried at all, nothing was learned of an element, and every choice
        // not tried is left as the walk of them left it.
        if (anElementCanBe || choices.each().isEmpty()) {
            refused.addAll(choices.rest().figures());
            unnamed.addAll(choices.rest().populations());
            unheld.addAll(choices.rest().unheld());
        }
        CompositionShortfall rest = CompositionShortfall.of(refused, unnamed, unheld);
        if (!built.isEmpty()) {
            return new TermRealizations.Realization.Built(built, rest);
        }
        if (!rest.figures().isEmpty()) {
            return new TermRealizations.Realization.Stopped(rest);
        }
        if (!rest.nothing()) {
            return new TermRealizations.Realization.Unexhausted(rest,
                    new SearchMessage.AnElementAStatementCouldNotBeReadAt(String.valueOf(unread)));
        }
        // No element can be at all, so the container of none is the one container there is, and
        // what an element would have turned on is nothing to choose by.
        if (!anElementCanBe) {
            return none(new SearchMessage.NoElementIsLeftAValue(String.valueOf(container)));
        }
        SearchMessage alone = chosenAlone(asked, container, apartAt);
        return alone != null ? notChosen(alone)
                : none(new SearchMessage.NoContainerMeetsEveryCount(String.valueOf(container)));
    }

    /**
     * Writes a container of {@code values} where, read whole ({@code all}), it meets everything
     * {@code asked} and every statement of its elements together; what the writing met is kept
     * beside what the composing met.
     *
     * @param heldTogether whether the way the elements were shared out already shows the
     *                     statements of the elements together hold, so they are not read again
     */
    private static void writtenIfAsked(List<ObservedValue> values,
                                          BorderQuantity.Observation all,
                                          List<Asked> asked, TermPath container,
                                          boolean heldTogether,
                                          List<AStatementAtARow> together, Standing standing,
                                          List<FixtureTemplate> built,
                                          Set<CompositionBudget> refused,
                                          Set<CompositionRepertoire> unnamed,
                                          Set<CompositionCapacity> unheld) {
        for (Asked each : asked) {
            // A count reads the container through the row and not the values handed it.
            if (!(each.over(container, List.of(), all) instanceof AStatementAtARow.Answer.Holds)) {
                return;
            }
        }
        if (!heldTogether && !heldTogether(together, container, all)) {
            return;
        }
        TermRealizations.Realization rows = standing.written(values, MOST_OFFERED - built.size());
        if (rows == null) {
            return;
        }
        if (rows instanceof TermRealizations.Realization.Built made) {
            made.values().forEach(built::add);
        }
        CompositionShortfall met = rows.shortfall();
        refused.addAll(met.figures());
        unnamed.addAll(met.populations());
        unheld.addAll(met.unheld());
    }

    /**
     * Where what an element answers of {@code asked} turns over at the number standing at
     * {@code place} inside it, with the numbers in {@code beside} standing where they are — or
     * null where some statement's turning could not be worked out.
     */
    private static List<ExactRatio> turnsOf(TermPath place, List<Asked> asked,
                                            Map<NumericTerm, Place> beside) {
        NumericTerm term = new NumericTerm.ValueOf(place);
        List<ExactRatio> out = new ArrayList<>();
        for (Asked one : asked) {
            List<ExactRatio> where = one.turnsAt(term, beside);
            if (where == null) {
                return null;
            }
            out.addAll(where);
        }
        return out;
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
    private static SearchMessage chosenAlone(List<Asked> asked, TermPath container,
                                      Quantity.TheValue under) {
        AStatementAtARow.TurnsOn turns = AStatementAtARow.TurnsOn.THE_ELEMENT;
        for (Asked each : asked) {
            turns = turns.orMore(each.turnsOnAmong(container, under));
        }
        return switch (turns) {
            case THE_ELEMENT, THOSE_UNDER_ITS_VALUE -> null;
            case THE_ORDER_OF_THOSE_UNDER_ITS_VALUE -> new SearchMessage.TurnsOnWhichIsHandedLast(
                    String.valueOf(container), String.valueOf(under));
            case OTHER_ELEMENTS -> under == null
                    ? new SearchMessage.TurnsOnTheElementsBesideIt(String.valueOf(container))
                    : new SearchMessage.TurnsOnElementsNotHoldingItsValue(
                            String.valueOf(container), String.valueOf(under));
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
     *                 that place shared among them, through what each element adds of it
     */
    private record TurningWith(List<NumericTerm> asItself, List<AddedOfIt> addedUp) {}

    /**
     * A total gathered under the value, and what an element adds to it of the number it turns
     * with: {@code weight} times the number, and {@code beside} — the form of the element's case,
     * where the case chooses the form.
     */
    private record AddedOfIt(NumericTerm total, ExactRatio weight, ExactRatio beside,
                             boolean fromTheLast) {

        /**
         * Where the number stands for one of {@code shared} elements to add a share of
         * {@code at}, or null where it stands nowhere. A total from the last element put is
         * shared by no element before that one, so it is what one element adds alone.
         */
        ExactRatio standingFor(ExactRatio at, int shared) {
            if (fromTheLast && shared != 1) {
                return null;
            }
            return at.dividedBy(ExactRatio.of(shared)).orNull() instanceof ExactRatio share
                    && share.minus(beside).orNull() instanceof ExactRatio left
                    ? left.dividedBy(weight).orNull() : null;
        }
    }

    private static TurningWith turningWith(NumericTerm term, Quantity.TheValue apartAt,
                                           List<Asked> asked) {
        List<NumericTerm> asItself = new ArrayList<>(List.of(term));
        List<AddedOfIt> addedUp = new ArrayList<>();
        if (apartAt == null) {
            return new TurningWith(asItself, addedUp);
        }
        for (Asked one : asked) {
            if (!(one instanceof Asked.SoManyMeeting(AStatementAtARow perElement, _, _, _))) {
                continue;
            }
            for (NumericTerm number : perElement.numbers()) {
                // Of the elements a statement keeps as well: the shares are where a kept element
                // is chosen, and whether it is kept is what reading the group says.
                if (!(number instanceof NumericTerm.GatheredUnderItsKey gathered)
                        || !apartAt.isWhereFiled(gathered.key(), gathered.elements())) {
                    continue;
                }
                ElementProjection place = ElementProjection.below(gathered.elements(),
                        term.subjectPath());
                // Each form an element's case may add through the place is a way the total comes
                // to a figure, so each is a place to stand at.
                for (ElementValue.Affine adds : place == null ? List.<ElementValue.Affine>of()
                        : addedThrough(gathered.value(), place)) {
                    ExactRatio weight = adds.form().coefs().get(place);
                    switch (gathered.gathering()) {
                        case NumericTerm.GatheredUnderItsKey.Gathering.End _ -> {
                            if (ExactRatio.ONE.equals(weight) && adds.form().constant().isZero()
                                    && !asItself.contains(number)) {
                                asItself.add(number);
                            }
                        }
                        case NumericTerm.GatheredUnderItsKey.Gathering.Total _,
                             NumericTerm.GatheredUnderItsKey.Gathering.SinceAPut _ -> {
                            AddedOfIt added = new AddedOfIt(number, weight,
                                    adds.form().constant(), gathered.gathering()
                                            instanceof NumericTerm.GatheredUnderItsKey.Gathering
                                                    .SinceAPut);
                            if (!addedUp.contains(added)) {
                                addedUp.add(added);
                            }
                        }
                    }
                }
            }
        }
        return new TurningWith(asItself, addedUp);
    }

    /**
     * What an element adds to a number gathered of {@code value}, where that is {@code place}
     * of it weighed and nothing else of it: the value itself, or the form of each case the place
     * is under, and of what no arm takes, each once — none where it is neither.
     */
    static List<ElementValue.Affine> addedThrough(ElementValue value, ElementProjection place) {
        return switch (value) {
            case ElementValue.Affine affine -> affine.form().coefs().size() == 1
                    && affine.form().coefs().get(place) instanceof ExactRatio weight
                    && weight.signum() != 0 ? List.of(affine) : List.of();
            case ElementValue.OfItsCase chosen -> {
                List<ElementValue> each = new ArrayList<>();
                chosen.arms().forEach(arm -> each.add(arm.value()));
                if (chosen.rest() != null) {
                    each.add(chosen.rest());
                }
                List<ElementValue.Affine> found = new ArrayList<>();
                for (ElementValue one : each) {
                    for (ElementValue.Affine form : addedThrough(one, place)) {
                        if (!found.contains(form)) {
                            found.add(form);
                        }
                    }
                }
                yield found;
            }
            default -> List.of();
        };
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
    static List<ObservedValue> numbersAt(TermPath at, OfTheType part, List<Asked> asked,
                                                 Quantity.TheValue apartAt, Quantities measuring,
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
                for (AddedOfIt added : turning.addedUp()) {
                    List<ExactRatio> where = one.turnsAt(added.total(), beside);
                    if (where == null) {
                        return null;
                    }
                    for (ExactRatio total : where) {
                        for (int shared = 1; shared <= MOST_ELEMENTS; shared++) {
                            ExactRatio standing = added.standingFor(total, shared);
                            if (standing != null) {
                                turns.add(standing);
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
            return none(new SearchMessage.NothingSaysHowOftenAnElementOccurs(
                    String.valueOf(container)));
        }
        NumericSet wanted = asked.walking();
        NumericSet size = null;
        if (manyItHolds != null) {
            AskedAt holds = demands.get(manyItHolds);
            if (holds == null || holds.walking() == null) {
                return none(new SearchMessage.NothingSaysHowManyElementsItHolds(
                        String.valueOf(container)));
            }
            size = holds.walking();
        }
        TypeView view = TypeView.of(sourceType, ruleSource.inners(), ruleSource.symbols(),
                ruleSource.kinds(), ruleSource.sums());
        if (!(view.shape() instanceof Shape.Sequence holding)
                || !container.element().outermostContainer().equals(container)) {
            return notChosen(new SearchMessage.NoListOrSetToHoldAnElementAsOften(
                    String.valueOf(container), String.valueOf(sourceType)));
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
            return notChosen(new SearchMessage.AnElementIsOnNoOrder(String.valueOf(container)));
        }
        NumericDomain.Bounds run = switch (within == null ? null : within.projectionOf(own)) {
            case NumericDomain.FormProjection.Within(NumericDomain.Bounds held) ->
                    held == null ? NumericDomain.Bounds.OPEN : held;
            case NumericDomain.FormProjection.NothingIsLeft _ -> null;
            case null -> NumericDomain.Bounds.OPEN;
        };
        if (run == null) {
            return none(new SearchMessage.NoValueForAnElement(String.valueOf(container)));
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
            return notChosen(new SearchMessage.WhereItTurnsOverCouldNotBeWorkedOut(
                    String.valueOf(kept.key()), String.valueOf(container)));
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
        return none(new SearchMessage.NoContainerHoldsAnElementAsOften(String.valueOf(container)));
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
                : List.of(new Asked.SoManyMeeting(kept.perElement(), ANY_COUNT, Optional.empty(),
                        Optional.empty()));
        Set<CompositionCapacity> unheld = new LinkedHashSet<>();
        Set<CompositionRepertoire> unnamed = EnumSet.noneOf(CompositionRepertoire.class);
        Map<NumericTerm, Place> beside = settledOutside(asked, container, within);
        List<List<String>> apart = ElementsKeptApart.at(view, keptApart, reading);
        Quantity.TheValue value = new Quantity.TheValue.AtAPlace(new DecisionSubject.AnInput(place));
        ListedByValue byValue = listedByValue(container, holding.element(), reading, value,
                (at, part) -> numbersAt(at, OfTheType.of(part, reading), asked, null, measuring,
                        within, beside, apart.isEmpty() ? 1 : MOST_ELEMENTS, unheld, unnamed,
                        reading.today()),
                (at, part) -> numbersAt(at, OfTheType.manyOf(part, reading), asked, null,
                        measuring, within, beside, MOST_ELEMENTS, unheld, unnamed,
                        reading.today()));
        if (byValue == null) {
            return notChosen(new SearchMessage.APartNeitherOneOfSoManyNorNumbers(
                    String.valueOf(container)));
        }
        if (byValue.values().isEmpty()) {
            return notChosen(new SearchMessage.AnElementIsAlikeAnother(String.valueOf(container),
                    String.valueOf(place)));
        }
        ElementValues ofTheElement = byValue.first();
        Set<CompositionBudget> refused = EnumSet.noneOf(CompositionBudget.class);
        if (!ofTheElement.listed().all()) {
            refused.add(CompositionBudget.VALUES_AN_ELEMENT_IS_CHOSEN_AMONG);
        }
        UnderEachValue under = UnderEachValue.of(byValue.values().size(), byValue.under(),
                values -> withNumbersBeside(ofTheElement.holding(sourceType, values), beside),
                container, value, asked, !apart.isEmpty(),
                UnderEachValue.oneEachUnder(container, value, apart), refused);
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
        SearchMessage alone = chosenAlone(asked, container, value);
        return alone != null ? notChosen(alone)
                : none(new SearchMessage.NoContainerHoldsAValueAtAsOften(
                        String.valueOf(container), String.valueOf(place)));
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
            return none(new SearchMessage.NothingSaysHowOftenAValueOccurs(String.valueOf(place)));
        }
        NumericSet wanted = asked.walking();
        List<TermPath> chain = place.containersHoldingIt();
        if (chain.size() < 2 || !place.equals(chain.getLast().element())) {
            return notChosen(new SearchMessage.AValueIsNotAnElementOfItsContainer(
                    String.valueOf(place)));
        }
        NumericTerm own = new NumericTerm.ValueOf(place);
        TermOrders orders = measuring.ordersOf(own);
        Carrier carrier = orders == null ? null : orders.observed();
        if (carrier == null) {
            return notChosen(new SearchMessage.AValueIsOnNoOrder(String.valueOf(place)));
        }
        NumericDomain.Bounds run = switch (within == null ? null : within.projectionOf(own)) {
            case NumericDomain.FormProjection.Within(NumericDomain.Bounds held) ->
                    held == null ? NumericDomain.Bounds.OPEN : held;
            case NumericDomain.FormProjection.NothingIsLeft _ -> null;
            case null -> NumericDomain.Bounds.OPEN;
        };
        if (run == null) {
            return none(new SearchMessage.NoValueAt(String.valueOf(place)));
        }
        Set<CompositionCapacity> unheld = new LinkedHashSet<>();
        Set<CompositionRepertoire> unnamed = EnumSet.noneOf(CompositionRepertoire.class);
        KeptOccurrences kept = term.selection();
        OfTheType leaves = OfTheType.of(
                NestedContainersAddingUp.ofTheLeaves(sourceType, place, reading), reading);
        List<Place> candidates = valuesToCount(kept, own, chain.getLast(), place, carrier, run,
                leaves, unheld, unnamed, reading.today());
        if (candidates == null) {
            return notChosen(new SearchMessage.WhereItTurnsOverCouldNotBeWorkedOut(
                    String.valueOf(kept.key()), String.valueOf(chain.getLast())));
        }
        if (candidates.isEmpty()) {
            return none(kept == null ? new SearchMessage.NoValueToRepeat(String.valueOf(place))
                    : new SearchMessage.NoValueToRepeatThatKeeps(String.valueOf(place),
                            String.valueOf(kept.key())));
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
                        beside.subList(0, extra), carrier, within, reading,
                        MOST_OFFERED - built.size());
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
        return unbuilt.came(rest, none(new SearchMessage.NoContainersHoldAValueAsOften(
                String.valueOf(place))));
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
                return none(new SearchMessage.NothingSaysHowOftenTheValueOccursAt(
                        String.valueOf(term.key()), String.valueOf(place)));
            }
            Place value = within == null ? null
                    : settled(within, new NumericTerm.ValueOf(term.key()));
            if (value == null) {
                return notChosen(new SearchMessage.StandsAtNoOneValue(String.valueOf(term.key())));
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
            return notChosen(new SearchMessage.AValueIsNotAnElementOfItsContainer(
                    String.valueOf(place)));
        }
        NumericTerm own = new NumericTerm.ValueOf(place);
        TermOrders orders = measuring.ordersOf(own);
        Carrier carrier = orders == null ? null : orders.observed();
        if (carrier == null) {
            return notChosen(new SearchMessage.AValueIsOnNoOrder(String.valueOf(place)));
        }
        NumericDomain.Bounds run = switch (within.projectionOf(own)) {
            case NumericDomain.FormProjection.Within(NumericDomain.Bounds held) ->
                    held == null ? NumericDomain.Bounds.OPEN : held;
            case NumericDomain.FormProjection.NothingIsLeft _ -> null;
            case null -> NumericDomain.Bounds.OPEN;
        };
        if (run == null) {
            return none(new SearchMessage.NoValueAt(String.valueOf(place)));
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
                (counted, others, room) -> nested.alike(sourceType, keptApart, counted, others,
                        carrier, within, reading, room));
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
        return search.unbuilt.came(rest, none(new SearchMessage.NoContainersHoldTheKeysAsOften(
                String.valueOf(place))));
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

        /** How a container is composed with the values counted and the others beside them, in at
         *  most {@code room} rows. */
        interface Composes {

            TermRealizations.Realization compose(List<NestedContainersAddingUp.Counted> counted,
                                                 List<Place> others, int room);
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
                TermRealizations.Realization one = composes.compose(List.copyOf(counted),
                        beside.subList(0, extra), MOST_OFFERED - built.size());
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
            BorderQuantity.Observation row = new AnElementRead(container, place,
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
    sealed interface Asked {

        /** Whether {@code value}, as the element {@code row} reads, answers this. */
        AStatementAtARow.Answer at(Place value, BorderQuantity.Observation row);

        /** Whether a container with {@code meeting} elements answering this has as many as this
         *  asks. */
        boolean asMany(int meeting);

        /** Where an element's answer to this turns over, with the numbers beside it where {@code
         *  beside} says; null where that could not be worked out. */
        List<ExactRatio> turnsAt(NumericTerm element, Map<NumericTerm, Place> beside);

        /** How many totals in a row {@code total} is tried at for an element of whole numbers to
         *  stand where this puts it ({@link AStatementAtARow#remaindersOf}). */
        int remaindersOf(NumericTerm total);

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
        boolean readsTheValueAt(TermPath container, Quantity.TheValue at);
        /** What an element of {@code container} answers of this turns on, the elements held as
         *  groups under one value at {@code under}, or each on its own where it is null
         *  ({@link AStatementAtARow#turnsOnAmong}). */
        AStatementAtARow.TurnsOn turnsOnAmong(TermPath container, Quantity.TheValue under);

        /**
         * How many elements meet {@code perElement}: one of the counts {@code wanted} holds.
         *
         * @param across the container whose elements each hold one of the containers whose
         *               elements are counted, where those are every element of all of them
         *               ({@link #composeAcross}): what an element turns on is asked of them all
         */
        record SoManyMeeting(AStatementAtARow perElement, LevelRegion wanted,
                             Optional<Quantity.TheValue> differentAt, Optional<TermPath> across)
                implements Asked {

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
            public boolean readsTheValueAt(TermPath container, Quantity.TheValue at) {
                return perElement.readsTheValueAt(container, at, across);
            }
            @Override
            public AStatementAtARow.TurnsOn turnsOnAmong(TermPath container,
                                                         Quantity.TheValue under) {
                return perElement.turnsOnAmong(container, under, across);
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
            public int remaindersOf(NumericTerm total) {
                return perElement.remaindersOf(total);
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

            /** Where what reads the number this asks of reads the value
             *  ({@link Quantity.TheValue#isReadAlong}). */
            @Override
            public boolean readsTheValueAt(TermPath container, Quantity.TheValue place) {
                return place.isReadAlong(at);
            }
            /** A number at one place inside the element. */
            @Override
            public AStatementAtARow.TurnsOn turnsOnAmong(TermPath container,
                                                         Quantity.TheValue under) {
                return AStatementAtARow.TurnsOn.THE_ELEMENT;
            }

            /** A value asked at an element reads no total. */
            @Override
            public int remaindersOf(NumericTerm total) {
                return 1;
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
    }

    /**
     * The numbers {@code asked} reads that are one number of the row and no number of
     * {@code container} as a whole, each at the one value the region leaves it at; a number the
     * region leaves at more or none is not among them.
     *
     * <p>One number of the row is what stands beside every element alike
     * ({@link NumbersOfTheWhole#oneNumberOfTheRow}): an input outside every container, or what
     * another container comes to. What is of this container as a whole is fixed with its elements
     * ({@link ContainerAsAWhole}) and does not stand beside them. A row of the container alone
     * holds none of these, so it is read holding them where they were fixed
     * ({@link #withNumbersBeside}).
     */
    static Map<NumericTerm, Place> settledOutside(List<Asked> asked, TermPath container,
                                                  SearchRegion within) {
        Map<NumericTerm, Place> out = new LinkedHashMap<>();
        for (Asked one : asked) {
            if (!(one instanceof Asked.SoManyMeeting(AStatementAtARow perElement, _, _, _))) {
                continue;
            }
            for (NumericTerm term : perElement.numbers()) {
                if (!NumbersOfTheWhole.standsBeside(term, container)) {
                    continue;
                }
                Place at = settled(within, term);
                if (at != null) {
                    out.put(term, at);
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
     * that one value, so an element of one stands where the same element of another does. Where
     * the element's case chooses the place, the value is held at the place of each case, so an
     * element of every case is listed holding it; the values are those the first such place is
     * chosen at.
     */
    private static ListedByValue listedByValue(
            TermPath container, Type element, RuleReadingContext reading, Quantity.TheValue place,
            BiFunction<TermPath, TypeView, List<ObservedValue>> numbers,
            BiFunction<TermPath, TypeView, List<ObservedValue>> valuesThere) {
        List<TermPath> heldAt = place == null ? List.of() : place.heldAt();
        List<List<ObservedValue>> valuesAt = new ArrayList<>();
        ElementValues first = ElementValues.of(container, element, reading, (at, part) -> {
            if (!heldAt.contains(at)) {
                return numbers.apply(at, part);
            }
            List<ObservedValue> values = valuesAt.isEmpty() ? valuesThere.apply(at, part)
                    : valuesAt.getFirst();
            if (values == null || values.isEmpty()) {
                return values;
            }
            if (valuesAt.isEmpty()) {
                valuesAt.add(values);
            }
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
                    (at, part) -> heldAt.contains(at) ? List.of(values.get(value))
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
                                 TermPath container, Quantity.TheValue at, List<Asked> asked,
                                 boolean once, boolean oneEach, Set<CompositionBudget> refused) {
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
                                                  Quantity.TheValue at) {
            for (Asked each : asked) {
                if (each.turnsOnAmong(container, at) != AStatementAtARow.TurnsOn.THE_ELEMENT) {
                    return false;
                }
                if (each instanceof Asked.SoManyMeeting(var _, var _,
                        Optional<Quantity.TheValue> differentAt, var _)
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
                        Optional<Quantity.TheValue> differentAt, var _) && differentAt.isPresent();
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
         * {@code value}, so that no value there is held by two of them: one of the places they are
         * kept apart at, {@code apart}, is that place, as fields from the element. A value the
         * element's case chooses the place of is kept apart by no such rule.
         */
        static boolean oneEachUnder(TermPath container, Quantity.TheValue value,
                                    List<List<String>> apart) {
            if (!(value instanceof Quantity.TheValue.AtAPlace(
                    DecisionSubject.AnInput(TermPath at, var _)))) {
                return false;
            }
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

    /** {@code row}, holding {@code beside} where there is any: a row asked once for each way the
     *  elements are shared out is not wrapped for nothing. */
    static BorderQuantity.Observation withNumbersBeside(
            BorderQuantity.Observation row, Map<NumericTerm, Place> beside) {
        return beside.isEmpty() ? row : new WithNumbersBeside(row, beside);
    }

    /**
     * A row holding the numbers beside its elements at the places they were fixed at, which a row
     * of the container alone does not hold ({@link BorderQuantity.Observation#fixedAt}).
     */
    private record WithNumbersBeside(BorderQuantity.Observation holding,
                                     Map<NumericTerm, Place> beside)
            implements BorderQuantity.Observation {

        @Override
        public WalkResult<ObservationAtPoint> at(TermPath path) {
            return holding.at(path);
        }

        @Override
        public Place fixedAt(NumericTerm term) {
            Place fixed = beside.get(term);
            return fixed != null ? fixed : holding.fixedAt(term);
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
                                        new WithNumbersBeside(each, beside))
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

        SearchMessage unreadSaid() {
            return new SearchMessage.AnElementAStatementCouldNotBeReadAt(String.valueOf(unread));
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
     * A row holding nothing but a container of these elements, read the way a row is.
     *
     * <p>Each element is a reading of its own ({@link #elements}), and the container is walked
     * through them. Anything else the statements ask for — a position this does not hold, the
     * elements of another container — could not be walked, which a statement reads as not being
     * able to tell and never as failing.
     */
    record AnElementRead(TermPath container, TermPath element,
                                 List<ObservedValue> held) implements BorderQuantity.Observation {

        /** Each element, read as this row with that element chosen. */
        List<BorderQuantity.Observation> elements() {
            List<BorderQuantity.Observation> out = new ArrayList<>();
            for (ObservedValue each : held) {
                out.add(new AnElementRead(container, element, List.of(each)));
            }
            return out;
        }

        @Override
        public WalkResult<ObservationAtPoint> at(TermPath path) {
            return path.equals(element) && held.size() == 1
                    ? WalkResult.reached(new ObservationAtPoint.Value(held.getFirst()))
                    : WalkResult.couldNotWalk();
        }

        /** Nothing is fixed beside the elements: the row holds them and nothing else. */
        @Override
        public Place fixedAt(NumericTerm term) {
            return null;
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

    static TermRealizations.Realization none(SearchMessage why) {
        return new TermRealizations.Realization.None(
                Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE, why);
    }

    /** Elements of a kind nothing here chooses, which is the population and no proof. */
    static TermRealizations.Realization notChosen(SearchMessage why) {
        return new TermRealizations.Realization.Unexhausted(CompositionShortfall.writing(
                Set.of(CompositionRepertoire.ELEMENTS_CHOSEN_FOR_A_COUNT)), why);
    }

    private CardinalityComposer() {}
}
