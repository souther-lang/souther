package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.check.DeclaredBounds;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.Shape;
import souther.compiler.check.TypeView;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermPath;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.types.Type;

import java.math.BigDecimal;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.stream.IntStream;

/**
 * Containers inside the elements of a container, filled so that every occurrence of a path inside
 * the innermost of them comes to a number.
 *
 * <p>{@link ContainersAddingUp} writes one number for each element of one container. Here an
 * element holds a container of its own, so it holds as many occurrences as that container does, and
 * the total is a total of the leaves. It is spread over as many leaves as the rules of every level
 * leave room for — the same spreading of a total over values a single container uses — and the
 * leaves are then grouped, one container at a time from the innermost out: each container holds the
 * leaves its level's count allows, and each element the container of the level below it.
 *
 * <p><b>The room is for every element the row carries.</b> The figure that says how many elements a
 * container is worth building with ({@link CompositionBudget#ELEMENTS_A_TOTAL_IS_SPREAD_OVER}) is
 * spent on the elements of every level together, and a grouping past it is never made — not
 * allocated and then refused. Spent on the leaves alone it would leave a container that must hold
 * a great many lists of nothing as large as its rules say, though no leaf is written.
 *
 * <p><b>The counts of every level are asked, and each is the container's own.</b> How many a level
 * holds is what its type declares tightened by what the rules leave on the way, as it is for one
 * container, and the grouping is made only where every level's count is met. A total no grouping
 * meets is said to be one the walk did not reach, since the groupings written here are two of the
 * many ({@link CompositionRepertoire#WAYS_A_TOTAL_IS_SPREAD}).
 *
 * <p>Each element is a whole value composed under its own type's rules with the container of the
 * level below written where the plan reaches it, so what the rest of an element holds is the plan's
 * question and not this one's.
 */
final class NestedContainersAddingUp {

    /** Every container the path is inside, outermost first, what each of them holds, and what its
     *  elements are kept apart at. */
    private record Level(TypeView view, Shape.Sequence holding, DeclaredBounds.CountRange howMany,
                         ContainersAddingUp.Ways ways, ContainersAddingUp.KeptApart apart) {}

    /**
     * How the leaves are grouped: for a container above the innermost, one entry for each element
     * it holds, each the container of the level below; for the innermost, how many leaves it
     * holds.
     */
    record Layout(List<Layout> within, int leaves) {

        /** Every element this writes, at every level: the leaves, and the elements each of them is
         *  held in, and the elements each of those is. */
        long elements() {
            long all = within.isEmpty() ? leaves : within.size();
            for (Layout each : within) {
                all += each.elements();
            }
            return all;
        }
    }

    /**
     * Whether a grouping was turned away for being past the room the figure leaves a row.
     *
     * <p>Told apart from a grouping that does not exist. What a walk owes a reader is which of the
     * two stopped it: a figure that was reached is somebody's to raise, and counts that no grouping
     * meets are not.
     */
    private static final class Cut {

        private boolean by;

        void reached() {
            by = true;
        }

        boolean by() {
            return by;
        }
    }

    private final TermPath run;

    NestedContainersAddingUp(TermPath run) {
        this.run = Objects.requireNonNull(run, "a run is read from somewhere");
    }

    TermRealizations.Realization to(Place answer, Type container, List<List<String>> keptApart,
                                    TermOrders orders, SearchRegion within,
                                    RuleReadingContext reading,
                                    ContainersAddingUp.HowManyIsAskedFor alsoHolding,
                                    DemandsInside inside) {
        Carrier elements = orders.answered();
        if (!(answer instanceof Count total) || elements == null) {
            return none(Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
        }
        if (!(within.projectionOf(new NumericTerm.ValueOf(run))
                instanceof NumericDomain.FormProjection.Within(NumericDomain.Bounds runs))) {
            return none(Generator.UnresolvedCombination.Reason.THE_RULES_LEAVE_NOTHING_THERE);
        }
        ContainersAddingUp.Ends ends = ContainersAddingUp.Ends.of(
                runs == null ? NumericDomain.Bounds.OPEN : runs, elements);
        if (ends == null) {
            return none(Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
        }
        ContainersAddingUp.WhatWasLeft left = new ContainersAddingUp.WhatWasLeft();
        List<TermPath> chain = run.containersHoldingIt();
        List<Level> levels = new ArrayList<>();
        Type type = container;
        // What the rules of the value holding each level's container keep its elements apart at:
        // the caller's for the outermost, and the element's above it for each one inside it.
        List<List<String>> held = keptApart;
        for (int at = 0; at < chain.size(); at++) {
            TermPath here = chain.get(at);
            TypeView view = TypeView.of(type, reading.source().inners(),
                    reading.source().symbols(), reading.source().kinds(), reading.source().sums());
            if (!(view.shape() instanceof Shape.Sequence holding)) {
                return none(Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
            }
            DeclaredBounds.CountRange howMany = ContainersAddingUp.howMany(view, here, within,
                    reading, at == 0 ? alsoHolding : null);
            if (howMany == null) {
                return none(Generator.UnresolvedCombination.Reason.THE_RULES_LEAVE_NOTHING_THERE);
            }
            boolean innermost = at == chain.size() - 1;
            // What each element is asked to hold is the number at the leaves in the innermost
            // container and the container of the level below in every other: one value of the
            // position, which is what the plan is made against.
            TermPath demand = innermost ? run : chain.get(at + 1);
            TermPath share = ContainersAddingUp.underTheCasesNamed(demand, inside.required());
            for (TermPath asked : inside.among().keySet()) {
                TermPath spelled = ContainersAddingUp.underTheCasesNamed(asked, inside.required());
                if (spelled.isAtOrUnder(share) || share.isAtOrUnder(spelled)) {
                    return new TermRealizations.Realization.Unexhausted(
                            CompositionShortfall.writing(Set.of(CompositionRepertoire
                                    .VALUES_THAT_ANSWER_SEVERAL_OF_THEIR_NUMBERS)),
                            "`" + asked + "` is asked for a value where an element holds the"
                                    + " containers the total is spread over");
                }
            }
            DemandsInside asked = at == 0 ? inside : DemandsInside.NOTHING;
            ContainersAddingUp.KeptApart apart = ContainersAddingUp.KeptApart.of(view, held,
                    holding.element(), here.element(), demand, asked.required(), reading);
            ContainersAddingUp.Ways ways = ContainersAddingUp.waysDown(holding.element(),
                    here.element(), demand, asked, apart, reading);
            if (ways.filled().isEmpty()) {
                return ways.cutBy().isEmpty()
                        ? new TermRealizations.Realization.None(
                                Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE,
                                ways.said(demand))
                        : new TermRealizations.Realization.Stopped(
                                CompositionShortfall.of(ways.cutBy()));
            }
            ways.cutBy().forEach(left::refused);
            levels.add(new Level(view, holding, howMany, ways, apart));
            if (!innermost) {
                held = ElementsKeptApart.heldUnder(holding.element(),
                        chain.get(at + 1).ruleKeyUnder(here.element()), reading);
                type = typeAlong(holding.element(), here, chain.get(at + 1), reading);
                if (type == null) {
                    return new TermRealizations.Realization.Unexhausted(
                            CompositionShortfall.writing(Set.of(
                                    CompositionRepertoire.WAYS_A_TOTAL_IS_SPREAD)),
                            "nothing here reads the way from `" + here + "` to `"
                                    + chain.get(at + 1) + "`");
                }
            }
        }
        ContainersAddingUp.WhatIsOffered offered = new ContainersAddingUp.WhatIsOffered();
        Walk walk = new Walk(total.at(), ends, levels, elements, alsoHolding, reading, offered,
                left);
        List<DeclaredBounds.CountRange> counts = levels.stream().map(Level::howMany).toList();
        long fewest = leaves(counts, 0, false);
        long most = leaves(counts, 0, true);
        if (fewest > most) {
            return none(Generator.UnresolvedCombination.Reason.THE_RULES_LEAVE_NOTHING_THERE);
        }
        ContainersAddingUp.asFarAs(ContainersAddingUp.countsAdmitted(
                new DeclaredBounds.CountRange(saturated(fewest), saturated(most)), null),
                walk, left);
        List<FixtureTemplate> built = offered.built();
        if (!built.isEmpty()) {
            return new TermRealizations.Realization.Built(built, left.shortfall());
        }
        CompositionShortfall met = left.shortfall();
        if (!met.figures().isEmpty()) {
            return new TermRealizations.Realization.Stopped(met);
        }
        // The groupings written here are some of the many, so nothing built is never a proof that
        // nothing does: it is said to be a population this walked some of.
        return new TermRealizations.Realization.Unexhausted(
                met.nothing() ? CompositionShortfall.writing(
                        Set.of(CompositionRepertoire.WAYS_A_TOTAL_IS_SPREAD)) : met,
                "no grouping of the leaves that this writes met the counts of every container on"
                        + " the way to `" + run + "`");
    }

    /**
     * The type of the container at {@code to}, a position inside the element {@code element} of the
     * container at {@code from}, or null where the way there is not fields all the way.
     */
    private static Type typeAlong(Type element, TermPath from, TermPath to,
                                  RuleReadingContext reading) {
        List<TermPath.Step> steps = to.steps().subList(from.steps().size() + 1, to.steps().size());
        Type at = element;
        for (TermPath.Step step : steps) {
            if (!(step instanceof TermPath.Step.Field field)) {
                return null;
            }
            TypeView view = TypeView.of(at, reading.source().inners(), reading.source().symbols(),
                    reading.source().kinds(), reading.source().sums());
            if (!(view.shape() instanceof Shape.Product product)) {
                return null;
            }
            at = product.fields().get(field.name());
            if (at == null) {
                return null;
            }
        }
        return at;
    }

    /** How many leaves a container of level {@code at} holds, at the fewest or at the most. */
    private static long leaves(List<DeclaredBounds.CountRange> counts, int at, boolean most) {
        DeclaredBounds.CountRange count = counts.get(at);
        long here = most ? count.most() : Math.max(count.least(), 0);
        if (at == counts.size() - 1) {
            return here;
        }
        return times(here, leaves(counts, at + 1, most));
    }

    /**
     * {@code one} times {@code other}, or the largest count there is where that is more.
     *
     * <p>The capacity of a level is a product of every level below it, and levels that say nothing
     * of the most they hold hold as many as a count can be. A product taken past that wraps round to
     * a number below the one asked for, and a level that holds everything is then read as holding
     * nothing — so every product of capacities is taken here, and the answer saturates upward,
     * which is the way a capacity is only ever compared.
     */
    private static long times(long one, long other) {
        return one == 0 || other == 0 ? 0 : one > Long.MAX_VALUE / other ? Long.MAX_VALUE
                : one * other;
    }

    /** {@code count} over {@code each}, rounded up, with no sum that could pass the end of a
     *  count. */
    private static long dividedUp(long count, long each) {
        return count / each + (count % each == 0 ? 0 : 1);
    }

    private static int saturated(long count) {
        return count > Integer.MAX_VALUE ? Integer.MAX_VALUE : (int) Math.max(count, 0);
    }

    /**
     * The groupings made of {@code leaves} leaves, and whether the room turned any other away.
     *
     * @param made    the groupings, none of them alike
     * @param refused whether a grouping the counts of the levels allow was not made for being past
     *                the room
     */
    record Groupings(List<Layout> made, boolean refused) {}

    /**
     * Every grouping this writes of {@code leaves} leaves into containers whose counts are
     * {@code counts}, outermost first, within {@code room} elements in all.
     *
     * <p>Every element of every level is one the row carries, so the room is for all of them
     * together and not for the leaves alone: a container that has to hold a great many lists of
     * nothing is as much to carry as one holding the same number of leaves.
     */
    static Groupings groupingsOf(List<DeclaredBounds.CountRange> counts, long leaves,
                                 ContainersAddingUp.HowManyIsAskedFor asked, long room) {
        List<Layout> made = new ArrayList<>();
        Cut cut = new Cut();
        for (boolean loadedFirst : new boolean[] {false, true}) {
            Layout one = layoutOf(counts, 0, leaves, loadedFirst, asked, room, cut);
            if (one != null && !made.contains(one)) {
                made.add(one);
            }
        }
        return new Groupings(List.copyOf(made), cut.by());
    }

    /**
     * The leaves {@code count} of them, grouped into the containers of the levels from {@code at}
     * down, or null where no grouping this writes meets every level's count.
     *
     * <p>Two groupings and both of the fewest elements the count of this level allows: the leaves
     * shared as evenly as the counts below allow, and every container below holding as few as it
     * may with what is left on the first. Which of the many groupings they are is not claimed.
     */
    private static Layout layoutOf(List<DeclaredBounds.CountRange> counts, int at, long count,
                                   boolean loadedFirst,
                                   ContainersAddingUp.HowManyIsAskedFor asked, long room,
                                   Cut cut) {
        DeclaredBounds.CountRange here = counts.get(at);
        long least = Math.max(here.least(), 0);
        if (at == counts.size() - 1) {
            if (count < least || count > here.most()
                    || (asked != null && !asked.holds((int) count))) {
                return null;
            }
            if (count > room) {
                cut.reached();
                return null;
            }
            return new Layout(List.of(), (int) count);
        }
        long eachFewest = leaves(counts, at + 1, false);
        long eachMost = leaves(counts, at + 1, true);
        long from = eachMost == 0 ? least : Math.max(least, dividedUp(count, eachMost));
        // Without a floor on what an element holds there is no number of elements the count
        // bounds, so a few of them are tried.
        long to = eachFewest == 0 ? Math.min(here.most(), from + 8)
                : Math.min(here.most(), count / eachFewest);
        for (long many = from; many <= to; many++) {
            if (times(many, eachMost) < count || times(many, eachFewest) > count
                    || (asked != null && !asked.holds((int) many))) {
                continue;
            }
            // Asked of a count of elements that the counts of this level and of the levels below
            // allow, and before anything is made: one past what is left of the room is a grouping
            // that was in front of the walk and is not built, and so is each count after it.
            if (many > room) {
                cut.reached();
                break;
            }
            List<Long> shares = shared(count, many, eachFewest, eachMost, loadedFirst);
            if (shares == null) {
                continue;
            }
            List<Layout> within = new ArrayList<>();
            long left = room - many;
            for (long share : shares) {
                Layout one = layoutOf(counts, at + 1, share, loadedFirst, null, left, cut);
                if (one == null) {
                    within = null;
                    break;
                }
                left -= one.elements();
                within.add(one);
            }
            if (within != null) {
                return new Layout(within, 0);
            }
        }
        return null;
    }

    /** {@code count} leaves over {@code many} elements, each holding between the two ends. */
    private static List<Long> shared(long count, long many, long fewest, long most,
                                     boolean loadedFirst) {
        if (many == 0) {
            return count == 0 ? List.of() : null;
        }
        List<Long> shares = new ArrayList<>();
        if (loadedFirst) {
            long spare = count - many * fewest;
            for (long i = 0; i < many; i++) {
                long more = Math.min(spare, most - fewest);
                shares.add(fewest + more);
                spare -= more;
            }
            return spare == 0 ? shares : null;
        }
        long base = count / many;
        long extra = count % many;
        for (long i = 0; i < many; i++) {
            shares.add(i < extra ? base + 1 : base);
        }
        return shares;
    }

    /** The counts of leaves walked from the fewest the rules leave, each spread and grouped. */
    private static final class Walk implements ContainersAddingUp.Spending<Integer> {

        private final BigDecimal total;
        private final ContainersAddingUp.Ends ends;
        private final List<Level> levels;
        private final List<DeclaredBounds.CountRange> counts;
        private final Carrier elements;
        private final ContainersAddingUp.HowManyIsAskedFor alsoHolding;
        private final RuleReadingContext reading;
        private final ContainersAddingUp.WhatIsOffered offered;
        private final ContainersAddingUp.WhatWasLeft left;

        Walk(BigDecimal total, ContainersAddingUp.Ends ends, List<Level> levels, Carrier elements,
             ContainersAddingUp.HowManyIsAskedFor alsoHolding, RuleReadingContext reading,
             ContainersAddingUp.WhatIsOffered offered, ContainersAddingUp.WhatWasLeft left) {
            this.total = total;
            this.ends = ends;
            this.levels = levels;
            this.counts = levels.stream().map(Level::howMany).toList();
            this.elements = elements;
            this.alsoHolding = alsoHolding;
            this.reading = reading;
            this.offered = offered;
            this.left = left;
        }

        @Override
        public Taken take(Integer count) {
            if (count > figure().maximum()) {
                return Taken.NOT_TAKEN;
            }
            Groupings groupings = groupingsOf(counts, count, alsoHolding, figure().maximum());
            // What the room turned away is said whether or not another grouping was made: that a
            // row was built is one fact, and that a piece in front of the walk was refused is
            // another, and a reader told only the first takes the offer for everything there was.
            if (groupings.refused()) {
                left.refused(figure());
            }
            List<Layout> layouts = groupings.made();
            // Nothing made says nothing of the counts after this one: the counts of a level can
            // leave this number of leaves no grouping at all and the next a small one, so only a
            // count of leaves past the room, which every grouping carries at least once over, ends
            // the counts.
            if (layouts.isEmpty()) {
                return Taken.AND_MORE;
            }
            // The groupings are some of the many, always.
            left.notAllOf(CompositionRepertoire.WAYS_A_TOTAL_IS_SPREAD);
            // No two leaves alike where any level keeps its elements apart by what they are built
            // around: leaves apart across the whole row are apart inside every container, and
            // containers holding leaves of their own are apart as wholes.
            boolean numbersApart = levels.stream().anyMatch(each -> each.apart().numbersApart());
            for (ContainersAddingUp.Spread how : ContainersAddingUp.Spread.values()) {
                switch (ContainersAddingUp.splitting(total, count, ends, how, elements,
                        numbersApart)) {
                    case ContainersAddingUp.Split.None _ -> { }
                    case ContainersAddingUp.Split.NotWorkedOut(var why) ->
                            left.unheld(new CompositionCapacity(
                                    CompositionCapacity.Where.VALUES_A_TOTAL_IS_SPREAD_OVER, why));
                    case ContainersAddingUp.Split.Some(List<BigDecimal> values) -> {
                        for (Layout layout : layouts) {
                            if (ContainersAddingUp.asFarAs(containers(values, layout), offered,
                                    left) == Traversal.STOPPED) {
                                return Taken.AND_DONE;
                            }
                        }
                    }
                }
            }
            return Taken.AND_MORE;
        }

        /** The containers this grouping of these values fills, one per way down. */
        private Iterable<FixtureTemplate> containers(List<BigDecimal> values, Layout layout) {
            int ways = levels.stream().mapToInt(each -> each.ways().filled().size()).max()
                    .orElse(0);
            return () -> IntStream.range(0, ways)
                    .mapToObj(way -> built(0, layout, new ArrayDeque<>(values), way))
                    .<FixtureTemplate>mapMulti((built, out) -> {
                        left.met(built.met());
                        built.values().forEach(out);
                    })
                    .iterator();
        }

        /**
         * The container of level {@code at} holding what {@code layout} says, taking the leaves it
         * holds off the front of {@code values}, or nothing where one of its elements cannot be
         * built — with what of this compiler's building them met.
         *
         * <p>Nothing as well where the elements of a container above the innermost are not apart as
         * its rules keep them. Leaves apart across the row put apart every container holding some,
         * and two holding none are alike all the same: a grouping this writes that does so is one
         * of the many it is not, which the walk says of every count.
         */
        private Proposals built(int at, Layout layout, Deque<BigDecimal> values, int way) {
            Level level = levels.get(at);
            List<ContainersAddingUp.Filling> fillings = level.ways().filled();
            ContainersAddingUp.Filling filling = fillings.get(Math.min(way, fillings.size() - 1));
            if (at == levels.size() - 1) {
                List<BigDecimal> mine = new ArrayList<>();
                for (int i = 0; i < layout.leaves(); i++) {
                    mine.add(values.removeFirst());
                }
                return ContainersAddingUp.filled(mine, level.holding(), level.view(), filling,
                        level.apart(), elements, reading);
            }
            List<FixtureTemplate> each = new ArrayList<>();
            List<Layout> within = layout.within();
            CompositionShortfall met = CompositionShortfall.NONE;
            for (int i = 0; i < within.size(); i++) {
                Proposals inner = built(at + 1, within.get(i), values, way);
                met = met.and(inner.met());
                Map<TermPath, FixtureTemplate> own = level.apart().besideFor(i, within.size());
                if (own == null) {
                    return new Proposals(List.of(), met.and(level.apart().met()));
                }
                if (inner.isEmpty()) {
                    return new Proposals(List.of(), met);
                }
                Map<TermPath, FixtureTemplate> beside = new LinkedHashMap<>(own);
                beside.putAll(filling.beside());
                Proposals one = PlanComposer.compose(filling.plan().root(),
                        new ValuesCarryingANumber(filling.fixed(), inner.values().getFirst(),
                                beside, filling.narrowed(), reading),
                        reading);
                met = met.and(one.met());
                if (one.isEmpty()) {
                    return new Proposals(List.of(), met);
                }
                each.add(one.values().getFirst());
            }
            if (!Witnesses.holdApart(each, level.apart().runs())) {
                return new Proposals(List.of(), met);
            }
            FixtureTemplate written = WornNames.under(level.view().wrappers(),
                    FixtureTemplate.collection(each), reading.source());
            return new Proposals(written == null ? List.of() : List.of(written), met);
        }

        @Override
        public CompositionBudget figure() {
            return CompositionBudget.ELEMENTS_A_TOTAL_IS_SPREAD_OVER;
        }
    }

    private static TermRealizations.Realization none(Generator.UnresolvedCombination.Reason why) {
        return new TermRealizations.Realization.None(why);
    }
}
