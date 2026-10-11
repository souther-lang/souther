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
import java.util.List;
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

    /** Every container the path is inside, outermost first, and what each of them holds. */
    private record Level(TypeView view, Shape.Sequence holding, DeclaredBounds.CountRange howMany,
                         ContainersAddingUp.Ways ways) {}

    /**
     * How the leaves are grouped: for a container above the innermost, one entry for each element
     * it holds, each the container of the level below; for the innermost, how many leaves it
     * holds.
     */
    private record Layout(List<Layout> within, int leaves) {}

    private final TermPath run;

    NestedContainersAddingUp(TermPath run) {
        this.run = Objects.requireNonNull(run, "a run is read from somewhere");
    }

    TermRealizations.Realization to(Place answer, Type container, TermOrders orders,
                                    SearchRegion within, RuleReadingContext reading,
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
            ContainersAddingUp.Ways ways = ContainersAddingUp.waysDown(holding.element(),
                    here.element(), demand, at == 0 ? inside : DemandsInside.NOTHING, reading);
            if (ways.filled().isEmpty()) {
                return ways.cutBy().isEmpty()
                        ? new TermRealizations.Realization.None(
                                Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE,
                                ways.said(demand))
                        : new TermRealizations.Realization.Stopped(
                                CompositionShortfall.of(ways.cutBy()));
            }
            ways.cutBy().forEach(left::refused);
            levels.add(new Level(view, holding, howMany, ways));
            if (!innermost) {
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
        long fewest = leaves(levels, 0, false);
        long most = leaves(levels, 0, true);
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
    private static long leaves(List<Level> levels, int at, boolean most) {
        DeclaredBounds.CountRange count = levels.get(at).howMany();
        long here = most ? count.most() : Math.max(count.least(), 0);
        if (at == levels.size() - 1) {
            return here;
        }
        long inner = leaves(levels, at + 1, most);
        return here == 0 || inner == 0 ? 0 : here > Long.MAX_VALUE / inner ? Long.MAX_VALUE
                : here * inner;
    }

    private static int saturated(long count) {
        return count > Integer.MAX_VALUE ? Integer.MAX_VALUE : (int) Math.max(count, 0);
    }

    /**
     * The leaves {@code count} of them, grouped into the containers of the levels from {@code at}
     * down, or null where no grouping this writes meets every level's count.
     *
     * <p>Two groupings and both of the fewest elements the count of this level allows: the leaves
     * shared as evenly as the counts below allow, and every container below holding as few as it
     * may with what is left on the first. Which of the many groupings they are is not claimed.
     */
    private static Layout layoutOf(List<Level> levels, int at, long count, boolean loadedFirst,
                                   ContainersAddingUp.HowManyIsAskedFor asked) {
        DeclaredBounds.CountRange here = levels.get(at).howMany();
        long least = Math.max(here.least(), 0);
        if (at == levels.size() - 1) {
            return count < least || count > here.most()
                    || (asked != null && !asked.holds((int) count)) ? null
                    : new Layout(List.of(), (int) count);
        }
        long eachFewest = leaves(levels, at + 1, false);
        long eachMost = leaves(levels, at + 1, true);
        long from = eachMost == 0 ? least
                : Math.max(least, (count + eachMost - 1) / Math.max(eachMost, 1));
        // Without a floor on what an element holds there is no number of elements the count
        // bounds, so a few of them are tried.
        long to = eachFewest == 0 ? Math.min(here.most(), from + 8)
                : Math.min(here.most(), count / eachFewest);
        for (long many = from; many <= to; many++) {
            if (many * eachMost < count || many * eachFewest > count
                    || (asked != null && !asked.holds((int) many))) {
                continue;
            }
            List<Long> shares = shared(count, many, eachFewest, eachMost, loadedFirst);
            if (shares == null) {
                continue;
            }
            List<Layout> within = new ArrayList<>();
            for (long share : shares) {
                Layout one = layoutOf(levels, at + 1, share, loadedFirst, null);
                if (one == null) {
                    within = null;
                    break;
                }
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
            List<Layout> layouts = new ArrayList<>();
            for (boolean loadedFirst : new boolean[] {false, true}) {
                Layout one = layoutOf(levels, 0, count, loadedFirst, alsoHolding);
                if (one != null && !layouts.contains(one)) {
                    layouts.add(one);
                }
            }
            if (layouts.isEmpty()) {
                return Taken.AND_MORE;
            }
            // The groupings are some of the many, always.
            left.notAllOf(CompositionRepertoire.WAYS_A_TOTAL_IS_SPREAD);
            for (ContainersAddingUp.Spread how : ContainersAddingUp.Spread.values()) {
                switch (ContainersAddingUp.splitting(total, count, ends, how, elements)) {
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
                    .filter(Objects::nonNull)
                    .iterator();
        }

        /**
         * The container of level {@code at} holding what {@code layout} says, taking the leaves it
         * holds off the front of {@code values}, or null where one of its elements cannot be built.
         */
        private FixtureTemplate built(int at, Layout layout, Deque<BigDecimal> values, int way) {
            Level level = levels.get(at);
            List<ContainersAddingUp.Filling> fillings = level.ways().filled();
            ContainersAddingUp.Filling filling = fillings.get(Math.min(way, fillings.size() - 1));
            if (at == levels.size() - 1) {
                List<BigDecimal> mine = new ArrayList<>();
                for (int i = 0; i < layout.leaves(); i++) {
                    mine.add(values.removeFirst());
                }
                return ContainersAddingUp.filled(mine, level.holding(), level.view(), filling,
                        elements, reading);
            }
            List<FixtureTemplate> each = new ArrayList<>();
            for (Layout below : layout.within()) {
                FixtureTemplate inner = built(at + 1, below, values, way);
                if (inner == null) {
                    return null;
                }
                FixtureTemplate one = PlanComposer.compose(filling.plan().root(),
                        new ValuesCarryingANumber(filling.fixed(), inner, filling.beside(),
                                filling.narrowed(), reading),
                        reading);
                if (one == null) {
                    return null;
                }
                each.add(one);
            }
            return WornNames.under(level.view().wrappers(), FixtureTemplate.collection(each),
                    reading.source());
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
