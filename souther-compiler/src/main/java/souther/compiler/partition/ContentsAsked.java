package souther.compiler.partition;

import souther.compiler.inputs.NameReach;
import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.TermPath;
import souther.compiler.observe.ElementsTaken;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;

/**
 * Which containers of a row are to hold the value at another position, and which are to hold
 * nothing equal to it — what the demands on a way ask that no region places.
 *
 * <p>Positions on both sides and no values. Which value stands at a position is known only once
 * the parameter it is under has been composed, and the container may be under another parameter
 * altogether; so this says what is asked, and the values are put in where the container is
 * composed ({@link #resolvedFor}).
 *
 * <p>Read off the demands and nowhere else: {@link RowDemand.SameAs} on some element is a value
 * written in, and {@link RowDemand.DifferentFrom} on every element is a value kept out. The other
 * two pairings are not composed here — some element unequal to a value, or every element equal to
 * one — and are said as not composed rather than left out.
 *
 * @param asked each container and the value it is to hold or hold nothing equal to, in the order
 *              the way asked them
 */
record ContentsAsked(List<Asked> asked) {

    /** Nothing asked. */
    static final ContentsAsked NONE = new ContentsAsked(List.of());

    ContentsAsked {
        asked = List.copyOf(asked);
    }

    /**
     * That the container at {@code container} holds the value at {@code value}, or holds nothing
     * equal to it — as an element, or as a key where {@code ofTheKey}.
     *
     * @param around the quantifier the demand on the container is asked under, where it is asked
     *               of a container inside an element: for each element of a container asked about
     *               every element, the demand is asked once more, and under one asking some element
     *               it is asked of the one chosen. One at most, since what is asked inside an
     *               element names no container further in ({@link RowDemand.WithinIt})
     */
    record Asked(TermPath container, TermPath value, boolean holding, boolean ofTheKey,
                 Optional<Around> around) {

        Asked {
            Objects.requireNonNull(container, "what is asked is asked of some container");
            Objects.requireNonNull(value, "a container is asked about the value at some position");
            Objects.requireNonNull(around, "asked under a quantifier or under none");
        }

        /**
         * Whether every row meeting the demand asks it: the quantifier around it, where there is
         * one, does not ask every element of its container, and so is not met by its container
         * holding none.
         */
        boolean inEveryRow() {
            return around.map(Around::some).orElse(true);
        }

        /**
         * Whether the plan of the container's parameter asks it as it is: every row meeting it asks
         * it, or the container is inside the element of the one the quantifier around it ranges
         * over. A plan writes such a container in every element it builds, so the demand is met in
         * each element there is and asked of nothing where there is none — and how many there are
         * is the plan's, not something to put in beforehand.
         */
        boolean askedOfThePlan() {
            return inEveryRow() || container.isAtOrUnder(around.orElseThrow().container().element());
        }

        /**
         * Whether a row composed this way has to have a value at {@link #value} to hand over: every
         * container it is inside is asked some element of by a quantifier every row meeting the
         * demand reaches — one with only such quantifiers around it — so each of them holds one in
         * any such row.
         *
         * <p>False says nothing about whether those containers hold anything — only that some row
         * meets the demand with one of them holding none, either because it is asked about every
         * element or because a quantifier around it is, and none of them is to be made to hold one
         * for the value's sake.
         */
        boolean standsWhereMet() {
            Set<TermPath> holdingOne = new LinkedHashSet<>();
            // The container's own quantifier is reached only where the one around it is, and
            // asks some element of it where it is to hold the value and every element where it is
            // to hold nothing equal to it.
            if (inEveryRow()) {
                around.ifPresent(outer -> holdingOne.add(outer.container()));
                if (holding) {
                    holdingOne.add(container);
                }
            }
            return holdingOne.containsAll(value.containersHoldingIt());
        }
    }

    /**
     * The quantifier a demand on a container inside an element is asked under.
     *
     * @param container the container it ranges over
     * @param some      whether it asks some element of it, rather than every one
     * @param from      the first element, in the order the container holds them, the demand is
     *                  asked of
     * @param below     the element after the last it is asked of, or {@link Integer#MAX_VALUE}
     *                  where it is asked of every element from {@code from} on. A count composed
     *                  with so many elements meeting a statement asks the statement of the first
     *                  so many and its denial of the rest ({@link ACountHandedOn})
     */
    record Around(TermPath container, boolean some, int from, int below) {

        Around {
            Objects.requireNonNull(container, "a quantifier ranges over a container");
            if (from < 0 || below < from || some && (from != 0 || below != Integer.MAX_VALUE)) {
                throw new IllegalArgumentException("a quantifier asks every element of a run, or"
                        + " some element of all of them: " + from + ".." + below);
            }
        }

        /** Asked of every element of {@code container}, or of some element where {@code some}. */
        static Around over(TermPath container, boolean some) {
            return new Around(container, some, 0, Integer.MAX_VALUE);
        }

        /** Whether the {@code element}-th element is one this asks the demand of. */
        boolean asksOf(int element) {
            return element >= from && element < below;
        }
    }

    /** What {@code way} asks of containers' contents. */
    static ContentsAsked of(List<OnTheWay.TakenIn> way) {
        List<Asked> out = new ArrayList<>();
        for (OnTheWay.TakenIn each : way) {
            switch (each.demand()) {
                // A count is composed with the container's other numbers, where its value is
                // written ({@link CardinalityComposer}), and asks no value written into it here.
                case RowDemand.Relational _, RowDemand.ATruth _, RowDemand.SoMany _,
                     RowDemand.ForTheRun _ -> { }
                case RowDemand.Exists exists -> asked(exists.container(), true,
                        exists.ofAnElement(), Optional.empty(), out);
                case RowDemand.ForAll every -> asked(every.container(), false,
                        every.ofEachElement(), Optional.empty(), out);
            }
        }
        return new ContentsAsked(out);
    }

    /**
     * What {@code way} asks of containers' contents, and what a count composed at {@code counts}
     * hands on for each element it counts ({@link ACountHandedOn}).
     */
    static ContentsAsked of(List<OnTheWay.TakenIn> way, Map<RealizationTarget, AskedAt> counts) {
        List<Asked> out = new ArrayList<>(of(way).asked());
        out.addAll(ACountHandedOn.askedOf(counts));
        return new ContentsAsked(out);
    }

    /**
     * What some element of {@code container} — or every one, not {@code some} — being asked
     * {@code ofTheElement} asks of the contents of containers: of this one, and of a container
     * inside its element, which a row writes alike in every element.
     *
     * @param around the quantifier this one is asked under, where it is asked inside an element
     */
    private static void asked(TermPath container, boolean some,
                              List<RowDemand.OfAnElement> ofTheElement, Optional<Around> around,
                              List<Asked> into) {
        Optional<Around> withThis = Optional.of(Around.over(container, some));
        for (RowDemand.OfAnElement one : ofTheElement) {
            switch (one) {
                case RowDemand.SameAs(TermPath value) when some ->
                        into.add(new Asked(container, value, true, false, around));
                case RowDemand.DifferentFrom(TermPath value) when !some ->
                        into.add(new Asked(container, value, false, false, around));
                case RowDemand.KeyedAs(TermPath value) when some ->
                        into.add(new Asked(container, value, true, true, around));
                case RowDemand.NotKeyedAs(TermPath value) when !some ->
                        into.add(new Asked(container, value, false, true, around));
                case RowDemand.WithinIt(TermPath inner, boolean innerSome, var asked) ->
                        asked(inner, innerSome, List.of(asked), withThis, into);
                case RowDemand.SameAs _, RowDemand.DifferentFrom _, RowDemand.KeyedAs _,
                     RowDemand.NotKeyedAs _, RowDemand.Relational _, RowDemand.ATruth _,
                     RowDemand.InCases _ -> { }
            }
        }
    }

    /**
     * What is asked, to be written under the cases a row that is already {@code trying} can be.
     *
     * <p><b>The place a container or a value is named is where a row writes it, except at a name
     * every case of a sum spreads</b> — worked out the one way every writer works it out
     * ({@link WhereANameIsWritten}). A container is a place a composer builds, so a place reached
     * is one to write at; what is left open is a case whose reading stopped. A container a
     * quantifier ranges over is written the same way, so that how many elements it holds is read
     * where the row writes it.
     *
     * <p><b>And what {@code trying} requires at such a name is written under a case the same
     * way.</b> A fork on {@code r.q.flag} requires the value there to be {@code Yes} whichever case
     * {@code r.q} is, and a row is one of them: the ways are the cases, each with the requirement
     * moved under it ({@link Requirements}). Walked together with the containers, because a row is
     * one case of a sum whichever of them put it there — a container and a requirement chosen
     * apart would ask for a value that is two cases at once.
     *
     * <p><b>And so is every other place the row writes a value it was asked for</b>
     * ({@code writing}): a {@code Bool} the way to a line read at a name the cases share is a
     * value written under the case the row is, along with everything else the row is.
     */
    UnderTheCases underTheCases(NameReach reach, Requirements trying, Set<TermPath> writing) {
        Set<TermPath> named = new LinkedHashSet<>();
        for (Asked each : asked) {
            named.add(each.container());
            named.add(each.value());
            each.around().ifPresent(around -> named.add(around.container()));
        }
        named.addAll(trying.atANameTheCasesShare());
        named.addAll(writing);
        List<TermPath> paths = List.copyOf(named);
        List<WhereANameIsWritten> written = new ArrayList<>();
        boolean notWorkedOut = false;
        for (TermPath each : paths) {
            WhereANameIsWritten one = WhereANameIsWritten.of(reach, each, trying, _ -> true);
            written.add(one);
            notWorkedOut |= one.someNotWorkedOut();
        }
        return new UnderTheCases(this, paths, written, trying, notWorkedOut);
    }

    /**
     * What is asked, with where under the cases each container and value of it may be written.
     *
     * <p>Tried a way at a time, and never laid out whole: the ways multiply by the cases of every
     * sum the names cross, each is a row composed whole, and the first that composes is the one a
     * row is written as. So they are handed to whoever composes them as they are reached, in the
     * order the model declares the cases, and the walk is held to a figure
     * ({@link CompositionBudget#WAYS_UNDER_THE_CASES_TRIED}).
     *
     * <p>Only ways a row can be at once: two names of one sum are written under one case, and a way
     * that put them under two would be a value that is both.
     *
     * @param named            every container and value asked, every container a quantifier
     *                         ranges over, every name the row is required something at that stands
     *                         under the cases, and every other place the row writes a value it was
     *                         asked for, each once
     * @param written          where each of {@code named} may be written
     * @param trying           what the row already is
     * @param someNotWorkedOut whether some way of writing one of them reached a case the row can be
     *                         whose reading stopped, so that what every tried way came to is not
     *                         every way there is
     */
    record UnderTheCases(ContentsAsked asked, List<TermPath> named,
                         List<WhereANameIsWritten> written, Requirements trying,
                         boolean someNotWorkedOut) {

        UnderTheCases {
            named = List.copyOf(named);
            written = List.copyOf(written);
        }

        /** How far handing the ways over went. */
        enum Walked {
            /** One of them composed, and none after it was handed over. */
            COMPOSED,
            /** Every way there was was handed over and none composed. */
            EVERY_WAY_TRIED,
            /** The figure was reached with ways still to hand over. */
            STOPPED_AT_THE_FIGURE
        }

        /**
         * One way of writing the row under the cases.
         *
         * @param contents what the containers are handed, at the places this way writes them
         * @param taken    what the row is taken to be to write it so: what it already was, every
         *                 case on the way to each place, and what was required at a name moved
         *                 under the case it is written as. That and not {@link #trying}, which is the
         *                 row before any case was chosen
         * @param standing where each of {@link #named} stands in this way
         */
        record Way(ContentsAsked contents, Requirements taken, Map<TermPath, TermPath> standing) {

            Way {
                standing = Map.copyOf(standing);
            }
        }

        /**
         * Hands each way to {@code composes}, until it answers that one composed or the figure is
         * reached.
         */
        Walked tryEach(Predicate<Way> composes) {
            int[] left = {CompositionBudget.WAYS_UNDER_THE_CASES_TRIED.maximum()};
            return from(0, trying, new LinkedHashMap<>(), composes, left);
        }

        private Walked from(int next, Requirements taken, Map<TermPath, TermPath> at,
                            Predicate<Way> composes, int[] left) {
            if (next == named.size()) {
                if (left[0] == 0) {
                    return Walked.STOPPED_AT_THE_FIGURE;
                }
                left[0]--;
                List<Asked> under = new ArrayList<>();
                for (Asked each : asked.asked()) {
                    under.add(new Asked(at.get(each.container()), at.get(each.value()),
                            each.holding(), each.ofTheKey(), each.around().map(around ->
                                    new Around(at.get(around.container()), around.some(),
                                            around.from(), around.below()))));
                }
                return composes.test(new Way(new ContentsAsked(under), taken, at))
                        ? Walked.COMPOSED : Walked.EVERY_WAY_TRIED;
            }
            for (WhereANameIsWritten.Place place : written.get(next).places()) {
                if (!(taken.merge(place.taken())
                        instanceof Requirements.Merge.Merged(Requirements both))) {
                    continue;
                }
                at.put(named.get(next), place.position());
                Walked walked = from(next + 1, both, at, composes, left);
                at.remove(named.get(next));
                if (walked != Walked.EVERY_WAY_TRIED) {
                    return walked;
                }
            }
            return Walked.EVERY_WAY_TRIED;
        }

        /**
         * What {@code walked} found out about the ways it did not try: the figure, where it stopped
         * there, and a way under a case the row can be whose reading stopped.
         *
         * <p>How far the walk went and nothing about what the ways came to. That is said by whoever
         * composed them, which knows what they came to ({@link WhatTheAlternativesCameTo}). Both
         * halves in the one value, so that neither travels beside it where a carrier may drop it.
         */
        SearchShortfall foundOut(Walked walked) {
            return SearchShortfall.of(walked == Walked.STOPPED_AT_THE_FIGURE
                            ? CompositionShortfall.of(
                                    Set.of(CompositionBudget.WAYS_UNDER_THE_CASES_TRIED))
                            : CompositionShortfall.NONE)
                    .unreadWhere(someNotWorkedOut);
        }
    }

    /**
     * What is asked of the containers of the parameter {@code head}, with the values the parameters
     * composed before it handed on put in.
     *
     * <p><b>A demand asked under a quantifier over every element is asked once for each element
     * there is.</b> What was a demand on positions is, once the container it ranges over is built,
     * a demand for each element it holds — the value read in each, or nothing where it holds none —
     * and the container asked is handed exactly those. So a container is made to hold a value only
     * where some row meeting the demand needs one there, and to hold each one such a row does.
     *
     * <p>A demand the plan asks as it is ({@link Asked#askedOfThePlan}) is handed to it whole: its
     * value is read off the positions the plan composes where it is this parameter's, and is the
     * one value handed on where it is another's. Any other demand under such a quantifier — over a
     * container of this parameter that the container asked is not inside an element of, or with
     * its value read off this parameter — has nothing built yet to say how many times it is asked.
     * It is not handed to the container, and it is kept as left open ({@link Here#leftOpen}): a
     * row composed without it is still the row's to take, and none being composed is no answer
     * about the model.
     *
     * <p>A quantifier asking a run of the elements ({@link Around#from}, {@link Around#below})
     * asks those, by their place in what was built.
     */
    Resolution resolvedFor(String head, ValuesHandedOn handed) {
        List<Asked> within = new ArrayList<>();
        List<Given> given = new ArrayList<>();
        List<Asked> leftOpen = new ArrayList<>();
        for (Asked each : asked) {
            if (!each.container().head().equals(head)) {
                continue;
            }
            if (each.askedOfThePlan()) {
                if (each.value().head().equals(head)) {
                    within.add(each);
                    continue;
                }
                List<ValuesHandedOn.Standing> standing = handed.values().get(each.value());
                if (standing == null) {
                    return new Resolution.Unresolved(nothingHandedOn(each.value()));
                }
                if (standing.size() != 1) {
                    return new Resolution.Unresolved(noOneValue(each.value(), standing.size()));
                }
                given.add(new Given(each, standing.getFirst().value()));
                continue;
            }
            // Asked under every element of a container: the one around it is over every element.
            Around around = each.around().orElseThrow();
            TermPath over = around.container();
            if (each.value().head().equals(head) || over.head().equals(head)) {
                leftOpen.add(each);
                continue;
            }
            List<ValuesHandedOn.Standing> standing = handed.values().get(each.value());
            if (standing == null) {
                return new Resolution.Unresolved(nothingHandedOn(each.value()));
            }
            List<ElementsTaken> held = handed.elements().get(over);
            if (held == null) {
                return new Resolution.Unresolved("nothing composed before hands on the elements `"
                        + over + "` holds");
            }
            // Each element, and the one value read in it: two read in one element are no one
            // value for it, as one read outside every element is the same for each.
            //
            // A value read inside an element took an element of every container the element did,
            // so it is filed under those once and looked up for each element, rather than every
            // value asked of every element. Only one read outside them is asked of each.
            List<TermPath> through = held.isEmpty() ? List.of()
                    : held.getFirst().outermostFirst().stream()
                            .map(ElementsTaken.Taken::container).toList();
            Map<List<Integer>, List<FixtureTemplate>> inside = new HashMap<>();
            List<ValuesHandedOn.Standing> outside = new ArrayList<>();
            for (ValuesHandedOn.Standing one : standing) {
                if (one.at().elementAt(over) == null) {
                    outside.add(one);
                } else {
                    inside.computeIfAbsent(elementsOf(one.at(), through),
                            _ -> new ArrayList<>()).add(one.value());
                }
            }
            for (ElementsTaken element : held) {
                if (!around.asksOf(element.elementAt(over))) {
                    continue;
                }
                List<FixtureTemplate> in = new ArrayList<>(
                        inside.getOrDefault(elementsOf(element, through), List.of()));
                for (ValuesHandedOn.Standing one : outside) {
                    if (one.at().agreesWith(element)) {
                        in.add(one.value());
                    }
                }
                if (in.size() != 1) {
                    return new Resolution.Unresolved(noOneValue(each.value(), in.size()));
                }
                given.add(new Given(each, in.getFirst()));
            }
        }
        return new Resolution.Resolved(new Here(within, given, leftOpen));
    }

    /** The element {@code taken} took from each of {@code through}, in that order. */
    private static List<Integer> elementsOf(ElementsTaken taken, List<TermPath> through) {
        List<Integer> out = new ArrayList<>();
        for (TermPath each : through) {
            out.add(taken.elementAt(each));
        }
        return out;
    }

    private static String nothingHandedOn(TermPath value) {
        return "a container is handed the value at `" + value + "`, and nothing composed before"
                + " handed it on";
    }

    private static String noOneValue(TermPath value, int found) {
        return found == 0
                ? "nothing stands at `" + value + "` in the value built"
                : "`" + value + "` is at each of " + found
                        + " elements of the value built, which is no one value";
    }

    /** What putting the values handed on into the demands on a parameter's containers came to. */
    sealed interface Resolution {

        /** What its containers are asked. */
        record Resolved(Here here) implements Resolution {}

        /** Why the values handed on do not say what one of them is to be handed. */
        record Unresolved(String why) implements Resolution {}
    }

    /**
     * A value handed on that a container is to hold, or to hold nothing equal to.
     *
     * @param asked the demand it was handed for
     * @param value the value
     */
    record Given(Asked asked, FixtureTemplate value) {

        Given {
            Objects.requireNonNull(asked, "a value is given for a demand");
            Objects.requireNonNull(value, "a value is given");
        }
    }

    /**
     * What the containers of one parameter are asked, with the values handed on put in.
     *
     * @param within the demands whose values are read off this parameter's own value, which the
     *               plan composes
     * @param given    the values handed on, each with the demand it was handed for
     * @param leftOpen the demands on its containers that nothing built yet says how many times
     *                 they are asked, and that are handed to nothing: a row composed without them
     *                 meets them or not as it comes, so what composing came to is not every row
     *                 there is
     */
    record Here(List<Asked> within, List<Given> given, List<Asked> leftOpen) {

        Here {
            within = List.copyOf(within);
            given = List.copyOf(given);
            leftOpen = List.copyOf(leftOpen);
        }

        /** Why what composing came to is not every row there is, or nothing where it is. */
        Optional<String> notComposed() {
            return leftOpen.stream().findFirst().map(each -> "`" + each.container() + "` is"
                    + " asked about `" + each.value() + "` for each element of `"
                    + each.around().orElseThrow().container() + "`, and nothing is built yet"
                    + " to say which elements that is, so it is not handed the value");
        }

        /**
         * What the container at {@code container} is handed, with each value read off this
         * parameter read by {@code valueAt} — or null where one of them has nothing standing for
         * it.
         *
         * <p>A key handed for a demand every row meeting it asks is filed over the element the
         * plan placed, where there is one, as it is asked of the one element some element is. One
         * handed for each element of a container asked about every element is a demand of its
         * own, on an entry of its own.
         */
        ContainerContents contentsOf(TermPath container,
                                     Function<TermPath, FixtureTemplate> valueAt) {
            List<FixtureTemplate> holding = new ArrayList<>();
            List<FixtureTemplate> keptOut = new ArrayList<>();
            List<FixtureTemplate> keysHeld = new ArrayList<>();
            List<FixtureTemplate> keysEachFiled = new ArrayList<>();
            List<FixtureTemplate> keysKeptOut = new ArrayList<>();
            for (Asked each : within) {
                if (!each.container().equals(container)) {
                    continue;
                }
                FixtureTemplate value = valueAt.apply(each.value());
                if (value == null) {
                    return null;
                }
                (each.ofTheKey() ? (each.holding() ? keysHeld : keysKeptOut)
                        : (each.holding() ? holding : keptOut)).add(value);
            }
            for (Given each : given) {
                Asked asked = each.asked();
                if (!asked.container().equals(container)) {
                    continue;
                }
                List<FixtureTemplate> into = asked.ofTheKey()
                        ? (!asked.holding() ? keysKeptOut
                                : asked.askedOfThePlan() ? keysHeld : keysEachFiled)
                        : (asked.holding() ? holding : keptOut);
                into.add(each.value());
            }
            return new ContainerContents(holding, keptOut, keysHeld, keysEachFiled, keysKeptOut);
        }
    }

    /**
     * What the plan of the parameter {@code head} has to hold for {@code here} to be composed: the
     * containers under it that are handed values, and the positions under it a value is read at —
     * for a container of its own or of another parameter's.
     *
     * <p>A value read for a demand the plan does not ask as it is is read off what was built,
     * element by element, and is no position the plan holds: a container holding none meets the
     * demand, and a position chosen inside it would make it hold one.
     */
    ConstructionPlan.ContentsComposed composedUnder(String head, Here here) {
        Set<TermPath> holdingOne = new LinkedHashSet<>();
        Set<TermPath> keepingOut = new LinkedHashSet<>();
        Set<TermPath> read = new LinkedHashSet<>();
        Set<TermPath> standing = new LinkedHashSet<>();
        Set<TermPath> aroundOne = new LinkedHashSet<>();
        Set<TermPath> aroundEach = new LinkedHashSet<>();
        List<Asked> handedHere = new ArrayList<>(here.within());
        here.given().forEach(each -> handedHere.add(each.asked()));
        for (Asked each : handedHere) {
            (each.holding() ? holdingOne : keepingOut).add(each.container());
            each.around().ifPresent(outer -> {
                if (each.container().isAtOrUnder(outer.container().element())) {
                    (outer.some() ? aroundOne : aroundEach).add(outer.container());
                }
            });
        }
        for (Asked each : asked) {
            if (each.askedOfThePlan() && each.value().head().equals(head)) {
                read.add(each.value());
                if (each.standsWhereMet()) {
                    standing.add(each.value());
                }
            }
        }
        return new ConstructionPlan.ContentsComposed(holdingOne, keepingOut, read, standing,
                aroundOne, aroundEach);
    }

    /**
     * What the value of one parameter is to hand on once it is built: the positions under it a
     * value is read at for a container of another parameter, and the containers under it a demand
     * on such a container is asked over every element of.
     *
     * @param one        the positions read as one value, by a demand every row meeting it asks
     * @param each       the positions read in each element of a container, by a demand asked
     *                   under every element of it, where it holds as many values as elements
     * @param containers the containers whose elements are counted
     */
    record ToHandOn(Set<TermPath> one, Set<TermPath> each, Set<TermPath> containers) {

        // In the order the way asked them: which of them a value built has nothing to hand on at
        // is said of the first, and that follows from it.
        ToHandOn {
            each = Collections.unmodifiableSet(new LinkedHashSet<>(each));
            Set<TermPath> once = new LinkedHashSet<>(one);
            once.removeAll(each);
            one = Collections.unmodifiableSet(once);
            containers = Collections.unmodifiableSet(new LinkedHashSet<>(containers));
        }

        /** Every position read, either way. */
        Set<TermPath> positions() {
            Set<TermPath> out = new LinkedHashSet<>(one);
            out.addAll(each);
            return out;
        }
    }

    /**
     * What the value of the parameter {@code head} hands on to the containers of other parameters
     * once it is composed.
     *
     * <p>Apart from {@link #composedUnder}'s, which also has the positions a container of this
     * parameter's own is handed. Those are read while the value is composed, out of what it is
     * being composed from, and nothing after it is handed them.
     */
    ToHandOn handedOnFrom(String head) {
        Set<TermPath> one = new LinkedHashSet<>();
        Set<TermPath> inEach = new LinkedHashSet<>();
        Set<TermPath> containers = new LinkedHashSet<>();
        for (Asked each : asked) {
            if (each.container().head().equals(head)) {
                continue;
            }
            if (each.value().head().equals(head)) {
                (each.askedOfThePlan() ? one : inEach).add(each.value());
            }
            if (!each.askedOfThePlan()) {
                TermPath over = each.around().orElseThrow().container();
                if (over.head().equals(head)) {
                    containers.add(over);
                }
            }
        }
        return new ToHandOn(one, inEach, containers);
    }

    /**
     * The positions under the parameter {@code head} a value is read at for a container of its
     * own: what composing that parameter reads out of what it is being composed from, before
     * anything builds it.
     */
    Set<TermPath> readWithin(String head) {
        Set<TermPath> out = new LinkedHashSet<>();
        for (Asked each : asked) {
            if (each.askedOfThePlan() && each.value().head().equals(head)
                    && each.container().head().equals(head)) {
                out.add(each.value());
            }
        }
        return out;
    }

    /**
     * Each parameter whose containers are handed a value read off another parameter, with those
     * others: the parameters it has to be composed after. A demand asked over every element of a
     * container of another parameter is asked as many times as that one holds elements, so it is
     * composed after that one too.
     */
    Map<String, Set<String>> composedAfter() {
        Map<String, Set<String>> out = new LinkedHashMap<>();
        for (Asked each : asked) {
            String container = each.container().head();
            Set<String> from = new LinkedHashSet<>();
            from.add(each.value().head());
            if (!each.askedOfThePlan()) {
                from.add(each.around().orElseThrow().container().head());
            }
            from.remove(container);
            if (!from.isEmpty()) {
                out.computeIfAbsent(container, _ -> new LinkedHashSet<>()).addAll(from);
            }
        }
        return out;
    }
}
