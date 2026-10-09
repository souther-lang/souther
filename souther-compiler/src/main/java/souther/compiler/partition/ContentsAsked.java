package souther.compiler.partition;

import souther.compiler.inputs.NameReach;
import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.TermPath;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
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
 * composed ({@link #contentsOf}).
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
     * equal to it.
     */
    record Asked(TermPath container, TermPath value, boolean holding) {}

    /** What {@code way} asks of containers' contents. */
    static ContentsAsked of(List<OnTheWay.TakenIn> way) {
        List<Asked> out = new ArrayList<>();
        for (OnTheWay.TakenIn each : way) {
            switch (each.demand()) {
                // A count is composed with the container's other numbers, where its value is
                // written ({@link CardinalityComposer}), and asks no value written into it here.
                case RowDemand.Relational _, RowDemand.ATruth _, RowDemand.SoMany _ -> { }
                case RowDemand.Exists exists -> {
                    for (RowDemand.OfAnElement one : exists.ofAnElement()) {
                        if (one instanceof RowDemand.SameAs(TermPath value)) {
                            out.add(new Asked(exists.container(), value, true));
                        }
                    }
                }
                case RowDemand.ForAll every -> {
                    for (RowDemand.OfAnElement one : every.ofEachElement()) {
                        if (one instanceof RowDemand.DifferentFrom(TermPath value)) {
                            out.add(new Asked(every.container(), value, false));
                        }
                    }
                }
            }
        }
        return new ContentsAsked(out);
    }

    /**
     * What is asked, to be written under the cases a row that is already {@code trying} can be.
     *
     * <p><b>The place a container or a value is named is where a row writes it, except at a name
     * every case of a sum spreads</b> — worked out the one way every writer works it out
     * ({@link WhereANameIsWritten}). A container is a place a composer builds, so a place reached
     * is one to write at; what is left open is a case whose reading stopped.
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
     * @param named            every container and value asked, every name the row is required
     *                         something at that stands under the cases, and every other place the
     *                         row writes a value it was asked for, each once
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
                            each.holding()));
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
     * What the plan of the parameter {@code head} has to hold for these to be composed: the
     * containers under it that are handed values, and the positions under it a value is read at —
     * for a container of its own or of another parameter's.
     */
    ConstructionPlan.ContentsComposed composedUnder(String head) {
        Set<TermPath> holdingOne = new LinkedHashSet<>();
        Set<TermPath> keepingOut = new LinkedHashSet<>();
        Set<TermPath> read = new LinkedHashSet<>();
        for (Asked each : asked) {
            if (each.container().head().equals(head)) {
                (each.holding() ? holdingOne : keepingOut).add(each.container());
            }
            if (each.value().head().equals(head)) {
                read.add(each.value());
            }
        }
        return new ConstructionPlan.ContentsComposed(holdingOne, keepingOut, read);
    }

    /**
     * The positions under the parameter {@code head} a value is read at for a container of another
     * parameter: what that parameter's value is to hand on once it is composed.
     *
     * <p>Apart from {@link #composedUnder}'s, which also has the positions a container of this
     * parameter's own is handed. Those are read while the value is composed, out of what it is
     * being composed from, and nothing after it is handed them.
     */
    Set<TermPath> handedOnFrom(String head) {
        return readUnder(head, false);
    }

    /**
     * The positions under the parameter {@code head} a value is read at for a container of its
     * own: what composing that parameter reads out of what it is being composed from, before
     * anything builds it.
     */
    Set<TermPath> readWithin(String head) {
        return readUnder(head, true);
    }

    private Set<TermPath> readUnder(String head, boolean byItsOwn) {
        Set<TermPath> out = new LinkedHashSet<>();
        for (Asked each : asked) {
            if (each.value().head().equals(head)
                    && each.container().head().equals(head) == byItsOwn) {
                out.add(each.value());
            }
        }
        return out;
    }

    /**
     * Each parameter whose containers are handed a value read off another parameter, with those
     * others: the parameters it has to be composed after.
     */
    Map<String, Set<String>> composedAfter() {
        Map<String, Set<String>> out = new LinkedHashMap<>();
        for (Asked each : asked) {
            String container = each.container().head();
            String value = each.value().head();
            if (!container.equals(value)) {
                out.computeIfAbsent(container, _ -> new LinkedHashSet<>()).add(value);
            }
        }
        return out;
    }

    /**
     * What the container at {@code container} is handed, with each value read by
     * {@code valueAt} — or null where one of them has nothing standing for it.
     */
    ContainerContents contentsOf(TermPath container,
                                 Function<TermPath, FixtureTemplate> valueAt) {
        List<FixtureTemplate> holding = new ArrayList<>();
        List<FixtureTemplate> keptOut = new ArrayList<>();
        for (Asked each : asked) {
            if (!each.container().equals(container)) {
                continue;
            }
            FixtureTemplate value = valueAt.apply(each.value());
            if (value == null) {
                return null;
            }
            (each.holding() ? holding : keptOut).add(value);
        }
        return new ContainerContents(holding, keptOut);
    }
}
