package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.TypeSymbol;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.function.Function;

/**
 * The numbers of a container as a whole that what its elements answer turns on — what they come
 * to at a place, how many there are — each fixed at a number before an element is chosen.
 *
 * <p><b>Fixed first, because an element's answer reads them.</b> A statement about an element that
 * reads the total of its container answers one way in a container coming to one total and another
 * way in another, so no element can be grouped by what it answers until the total is a number.
 * With every one of them fixed, each is a number beside the element as any input's is, and where
 * the element's own numbers turn over is worked out against it ({@link AStatementAtARow#turnsAt}).
 *
 * <p><b>An element read in a container of so many coming to those numbers.</b> A row holding the
 * elements of a group alone comes to what they come to, which is not the number fixed. So the group
 * is read with its own places answered by the row holding it and the container's whole numbers
 * answered by a row of as many elements coming to what is fixed: the group, one element holding
 * what is left of each total, and elements holding nought ({@link Fixed#readingOf}). What is read of the
 * container through that row is what the container chosen will come to, which is what the reading
 * of the group is for.
 *
 * <p><b>Then the elements are moved to come to it.</b> The elements a sharing draws are the values
 * they were listed at, and a total of them is whatever those come to. Each is moved at every place
 * a total adds up, inside the run of that place its answers hold over — between the numbers that
 * place turns over at — until the elements come to what was fixed ({@link Fixed#spread}). What
 * comes of that is read again whole before it is offered, as every container is.
 */
final class ContainerAsAWhole {

    /** The most whole numbers a total the statements read and nothing fixes is tried at. */
    private static final int MOST_TOTALS =
            CompositionBudget.TOTALS_A_COUNT_IS_TRIED_AT.maximum();

    private static final int MOST_ELEMENTS =
            CompositionBudget.ELEMENTS_A_COUNT_IS_COMPOSED_WITH.maximum();

    /**
     * A total the row asks of the container, and the numbers it is tried at.
     *
     * @param term  the total
     * @param tried the numbers the demand on it leaves, as its builder hands them over
     */
    record ATotal(NumericTerm term, TermRealizations.Tried tried) {

        ATotal {
            Objects.requireNonNull(term, "a total is a number");
            Objects.requireNonNull(tried, "a total is tried at some numbers");
        }
    }

    /**
     * One number of the container as a whole and the numbers it is tried at.
     *
     * @param term    the number
     * @param added   what each element adds to it, where it is a total; null for how many there are
     * @param carrier the order each element's number at the place a total adds up is written on;
     *                null for how many there are
     */
    private record OneNumber(NumericTerm term, NumbersOfTheWhole.AddedUp added, Carrier carrier,
                             TermRealizations.Tried tried) {}

    private final TermPath container;
    private final List<OneNumber> numbers;
    /** Whether a statement reads how many the container holds, which then stands beside an
     *  element as the totals do. */
    private final boolean sizeIsRead;

    private ContainerAsAWhole(TermPath container, List<OneNumber> numbers, boolean sizeIsRead) {
        this.container = container;
        this.numbers = List.copyOf(numbers);
        this.sizeIsRead = sizeIsRead;
    }

    /** Whether nothing of the container as a whole is fixed, which is every count that reads only
     *  its elements and what stands beside them. */
    boolean isEmpty() {
        return numbers.isEmpty();
    }

    /**
     * What the row asks of {@code container} as a whole — {@code totals}, and {@code size} where how
     * many it holds is read — and what the statements {@code asked} read of it, or null where one
     * of them is a number this does not fix: a total of a place whose elements are not written on
     * whole numbers.
     *
     * <p>A total the statements read and the row does not ask is tried at the whole numbers
     * nearest nought first: any number does, the elements being moved to come to it, so the
     * nearest are the ones least likely to leave an element past what its type admits. How many
     * the container holds is fixed where a statement reads it, or where a total is of a form of
     * its elements' numbers, which comes to so much more for each element it holds.
     */
    static ContainerAsAWhole of(TermPath container, List<CardinalityComposer.Asked> asked,
                                List<ATotal> totals, NumericSet size, Quantities measuring) {
        Map<NumericTerm, OneNumber> out = new LinkedHashMap<>();
        boolean howManyIsRead = false;
        for (ATotal each : totals) {
            NumbersOfTheWhole.AddedUp added = NumbersOfTheWhole.addedUp(each.term());
            Carrier carrier = carrierAt(added, measuring);
            if (added == null || carrier == null) {
                return null;
            }
            out.put(each.term(), new OneNumber(each.term(), added, carrier, each.tried()));
        }
        NumericTerm many = null;
        for (CardinalityComposer.Asked each : asked) {
            if (!(each instanceof CardinalityComposer.Asked.SoManyMeeting meeting)) {
                continue;
            }
            for (NumericTerm term : meeting.perElement().numbers()) {
                if (!container.equals(NumbersOfTheWhole.containerOf(term))) {
                    continue;
                }
                if (NumbersOfTheWhole.howManyItHolds(term, container)) {
                    howManyIsRead = true;
                    many = term;
                    continue;
                }
                if (out.containsKey(term)) {
                    continue;
                }
                NumbersOfTheWhole.AddedUp added = NumbersOfTheWhole.addedUp(term);
                Carrier carrier = carrierAt(added, measuring);
                if (carrier == null) {
                    return null;
                }
                out.put(term, new OneNumber(term, added, carrier, nearestNoughtFirst()));
            }
        }
        boolean formed = out.values().stream().anyMatch(each ->
                !each.added().weight().equals(ExactRatio.ONE) || !each.added().constant().isZero());
        if (howManyIsRead || formed) {
            NumericTerm counted = many != null ? many
                    : new NumericTerm.ValueOf(container);
            out.put(counted, new OneNumber(counted, null, null, sizes(size)));
        }
        return new ContainerAsAWhole(container, new ArrayList<>(out.values()), howManyIsRead);
    }

    /** The order the numbers at the place a total adds up are written on, where it counts in
     *  whole numbers — the elements are moved by whole steps to come to the total. */
    private static Carrier carrierAt(NumbersOfTheWhole.AddedUp added, Quantities measuring) {
        if (added == null) {
            return null;
        }
        TermOrders orders = measuring.ordersOf(new NumericTerm.ValueOf(added.place()));
        Carrier carrier = orders == null ? null : orders.observed();
        return carrier != null && carrier.countsInWholeNumbers() ? carrier : null;
    }

    /** The whole numbers nearest nought first, as many as a total is tried at. */
    private static TermRealizations.Tried nearestNoughtFirst() {
        List<Place> out = new ArrayList<>();
        for (int at = 0; out.size() < MOST_TOTALS; at++) {
            out.add(Count.of(at));
            if (at != 0 && out.size() < MOST_TOTALS) {
                out.add(Count.of(-at));
            }
        }
        return new TermRealizations.Tried(out, new TermRealizations.Remainder.StoppedAt(
                CompositionBudget.TOTALS_A_COUNT_IS_TRIED_AT));
    }

    /** How many the container may hold, from none up to the most a count composes it with. */
    private static TermRealizations.Tried sizes(NumericSet size) {
        List<Place> out = new ArrayList<>();
        for (int many = 0; many <= MOST_ELEMENTS; many++) {
            if (size == null || size.holds(Count.of(many), Carrier.WHOLE)) {
                out.add(Count.of(many));
            }
        }
        return new TermRealizations.Tried(out, new TermRealizations.Remainder.StoppedAt(
                CompositionBudget.ELEMENTS_A_COUNT_IS_COMPOSED_WITH));
    }

    /**
     * Every choice of a number for each number of the whole, up to the figure the choices of
     * several totals are held to, and why there are no more.
     */
    TermRealizations.Together choices() {
        List<TermRealizations.Tried> each = new ArrayList<>();
        for (OneNumber one : numbers) {
            each.add(one.tried());
        }
        return TermRealizations.Together.of(each);
    }

    /**
     * The numbers of the whole at one choice, in the order {@link #choices} hands them. How many
     * the container holds stands beside an element only where a statement reads it.
     */
    Fixed at(List<Place> chosen) {
        Map<NumericTerm, Place> fixed = new LinkedHashMap<>();
        Integer many = null;
        for (int each = 0; each < numbers.size(); each++) {
            OneNumber one = numbers.get(each);
            if (one.added() != null) {
                fixed.put(one.term(), chosen.get(each));
                continue;
            }
            for (int held = 0; held <= MOST_ELEMENTS; held++) {
                if (Count.number(chosen.get(each)).at().compareTo(BigDecimal.valueOf(held)) == 0) {
                    many = held;
                }
            }
            if (sizeIsRead) {
                fixed.put(one.term(), chosen.get(each));
            }
        }
        return new Fixed(fixed, many);
    }

    /**
     * The numbers of the container as a whole at one choice of each, and how many elements it
     * holds where that is fixed.
     */
    final class Fixed {

        private final Map<NumericTerm, Place> fixed;
        private final Integer many;

        private Fixed(Map<NumericTerm, Place> fixed, Integer many) {
            this.fixed = Map.copyOf(fixed);
            this.many = many;
        }

        /** How many the container holds, or null where that is not fixed. */
        Integer many() {
            return many;
        }

        /** {@code beside} with every number of the whole standing where it is fixed. */
        Map<NumericTerm, Place> beside(Map<NumericTerm, Place> beside) {
            Map<NumericTerm, Place> out = new LinkedHashMap<>(beside);
            out.putAll(fixed);
            return out;
        }

        /**
         * {@code group}, as {@code holding} reads a container of it, read inside a container of as
         * many elements as are fixed coming to every total fixed — or null where no container of so
         * many holds the group.
         */
        BorderQuantity.Observation readingOf(
                List<ObservedValue> group,
                Function<List<ObservedValue>, BorderQuantity.Observation> holding) {
            List<ObservedValue> whole = aroundIt(group);
            if (whole == null) {
                return null;
            }
            return new InsideTheWhole(holding.apply(group), holding.apply(whole), container);
        }

        /**
         * The group and, where the container holds more, one element holding what is left of
         * every total and elements holding nought at every place a total adds up.
         */
        private List<ObservedValue> aroundIt(List<ObservedValue> group) {
            int held = many != null ? many : group.size() + 1;
            if (held < group.size() || group.isEmpty()) {
                return held == group.size() ? group : null;
            }
            if (held == group.size()) {
                return group;
            }
            ObservedValue left = group.getFirst();
            ObservedValue nought = group.getFirst();
            for (OneNumber one : numbers) {
                if (one.added() == null) {
                    continue;
                }
                List<TermPath.Step> steps = stepsInside(one.added().place());
                BigInteger owed = owed(one, Count.number(fixed.get(one.term())), held);
                if (steps == null || owed == null) {
                    return null;
                }
                for (ObservedValue each : group) {
                    BigInteger at = wholeAt(each, steps, one.carrier());
                    if (at == null) {
                        return null;
                    }
                    owed = owed.subtract(at);
                }
                left = placedAt(left, steps, one.carrier().valueOf(Count.of(new BigDecimal(owed))));
                nought = placedAt(nought, steps, one.carrier().valueOf(Count.of(0)));
                if (left == null || nought == null) {
                    return null;
                }
            }
            List<ObservedValue> out = new ArrayList<>(group);
            out.add(left);
            while (out.size() < held) {
                out.add(nought);
            }
            return out;
        }

        /**
         * {@code drawn} with each element moved at every place a total adds up, inside the run of
         * that place it was listed in, so that the elements come to every total fixed — or null
         * where they do not.
         *
         * <p>An element may start from any value it answers alike to, which {@code alike} lists
         * for it: the values of a group answer every statement the same, and the run one of them
         * stands in may reach where another's does not. Each starts from one whose run goes
         * furthest the way the total is still owed — the {@code variant}-th of those that go as
         * far, since the values of a group are alike to the statements and not to the type, which
         * may tie a place no statement reads to the number moved.
         *
         * @param alike   for each element drawn, the values it answers alike to, or null where it
         *                is to start from where it was drawn
         * @param variant which of the starts going as far each element takes
         * @param turns  where each place a total adds up turns over, with every number of the
         *               whole standing where it is fixed; null at a place where that could not be
         *               worked out, which leaves the elements where they were listed
         * @param region what the rules leave each such place
         */
        List<ObservedValue> spread(List<ObservedValue> drawn, List<List<ObservedValue>> alike,
                                   int variant, Function<TermPath, List<ExactRatio>> turns,
                                   Function<TermPath, NumericDomain.Bounds> region) {
            List<ObservedValue> out = new ArrayList<>(drawn);
            for (OneNumber one : numbers) {
                if (one.added() == null) {
                    continue;
                }
                List<TermPath.Step> steps = stepsInside(one.added().place());
                BigInteger target = owed(one, Count.number(fixed.get(one.term())), out.size());
                if (steps == null || target == null) {
                    return null;
                }
                List<ExactRatio> where = turns.apply(one.added().place());
                WholeNumbersLeft left = WholeNumbersLeft.of(region.apply(one.added().place()));
                BigInteger sum = BigInteger.ZERO;
                for (ObservedValue each : out) {
                    BigInteger at = wholeAt(each, steps, one.carrier());
                    if (at == null) {
                        return null;
                    }
                    sum = sum.add(at);
                }
                int owing = target.compareTo(sum);
                BigInteger[] at = new BigInteger[out.size()];
                BigInteger[][] runs = new BigInteger[out.size()][];
                sum = BigInteger.ZERO;
                for (int each = 0; each < at.length; each++) {
                    List<ObservedValue> starts = alike == null || alike.get(each) == null
                            ? List.of(out.get(each)) : alike.get(each);
                    // Every start whose run goes furthest, and then the variant-th of them.
                    List<ObservedValue> furthest = new ArrayList<>();
                    List<BigInteger> from = new ArrayList<>();
                    for (ObservedValue start : starts) {
                        BigInteger value = wholeAt(start, steps, one.carrier());
                        if (value == null) {
                            continue;
                        }
                        BigInteger[] run = where == null ? new BigInteger[] {value, value}
                                : runOf(value, where, left);
                        if (runs[each] == null || further(run, runs[each], owing)) {
                            runs[each] = run;
                            furthest.clear();
                            from.clear();
                        }
                        if (!further(runs[each], run, owing)) {
                            furthest.add(start);
                            from.add(value);
                        }
                    }
                    if (runs[each] == null) {
                        return null;
                    }
                    int taken = variant % furthest.size();
                    out.set(each, furthest.get(taken));
                    at[each] = from.get(taken);
                    runs[each] = where == null ? new BigInteger[] {at[each], at[each]}
                            : runOf(at[each], where, left);
                    sum = sum.add(at[each]);
                }
                BigInteger delta = target.subtract(sum);
                for (int each = 0; each < at.length && delta.signum() != 0; each++) {
                    BigInteger edge = runs[each][delta.signum() > 0 ? 1 : 0];
                    BigInteger reach = edge == null ? delta : edge.subtract(at[each]);
                    BigInteger step = delta.signum() > 0 ? delta.min(reach) : delta.max(reach);
                    at[each] = at[each].add(step);
                    delta = delta.subtract(step);
                }
                if (delta.signum() != 0) {
                    return null;
                }
                for (int each = 0; each < at.length; each++) {
                    ObservedValue moved = placedAt(out.get(each), steps,
                            one.carrier().valueOf(Count.of(new BigDecimal(at[each]))));
                    if (moved == null) {
                        return null;
                    }
                    out.set(each, moved);
                }
            }
            return out;
        }

        /**
         * What the numbers at the place {@code one} adds up are to come to across {@code held}
         * elements for it to stand at {@code total}: the total less what the elements add beside
         * their numbers, over the weight — or null where that is no whole number.
         */
        private BigInteger owed(OneNumber one, Count total, int held) {
            ExactAnswer<ExactRatio> owed = one.added().constant().times(ExactRatio.of(held))
                    .flatMap(beside -> total.exactly().minus(beside))
                    .flatMap(left -> left.dividedBy(one.added().weight()));
            return owed instanceof ExactAnswer.Held<ExactRatio>(ExactRatio whole) && whole.isWhole()
                    && whole.floor() instanceof ExactAnswer.Held<BigInteger>(BigInteger at)
                    ? at : null;
        }
    }

    /**
     * Whether {@code run} reaches further than {@code than} the way {@code owing} says: up where
     * it is above nought, down where it is below, and neither where nothing is owed. An open end
     * reaches furthest.
     */
    private static boolean further(BigInteger[] run, BigInteger[] than, int owing) {
        if (owing == 0) {
            return false;
        }
        BigInteger end = run[owing > 0 ? 1 : 0];
        BigInteger other = than[owing > 0 ? 1 : 0];
        if (other == null) {
            return false;
        }
        return end == null || (owing > 0 ? end.compareTo(other) > 0 : end.compareTo(other) < 0);
    }

    /** The steps from an element of the container to {@code place}, or null where it is not
     *  inside one, or is reached by a step no element value is walked by here. */
    private List<TermPath.Step> stepsInside(TermPath place) {
        TermPath element = container.element();
        if (!place.isAtOrUnder(element)) {
            return null;
        }
        List<TermPath.Step> below = place.steps().subList(element.steps().size(),
                place.steps().size());
        for (TermPath.Step step : below) {
            if (!(step instanceof TermPath.Step.Field)) {
                return null;
            }
        }
        return below;
    }

    /**
     * The whole numbers {@code at} can be moved to and still answer as it does: between the
     * nearest number its place turns over at on either side, or at that number where it stands on
     * one, and inside what the rules leave the place. An end that is null is open.
     */
    private static BigInteger[] runOf(BigInteger at, List<ExactRatio> turns,
                                      WholeNumbersLeft left) {
        ExactRatio here = ExactRatio.of(new BigDecimal(at));
        BigInteger low = left.least();
        BigInteger high = left.most();
        for (ExactRatio turn : turns) {
            int side = turn.compareTo(here);
            if (side == 0) {
                return new BigInteger[] {at, at};
            }
            if (side < 0 && turn.floor() instanceof ExactAnswer.Held<BigInteger>(BigInteger down)) {
                BigInteger above = down.add(BigInteger.ONE);
                low = low == null || above.compareTo(low) > 0 ? above : low;
            }
            if (side > 0 && turn.ceiling() instanceof ExactAnswer.Held<BigInteger>(BigInteger up)) {
                BigInteger below = up.subtract(BigInteger.ONE);
                high = high == null || below.compareTo(high) < 0 ? below : high;
            }
        }
        return new BigInteger[] {low, high};
    }

    /** The whole number {@code element} holds {@code steps} inside it, or null where it holds none
     *  there. */
    private static BigInteger wholeAt(ObservedValue element, List<TermPath.Step> steps,
                                      Carrier carrier) {
        ObservedValue at = element;
        for (TermPath.Step step : steps) {
            if (!(at instanceof ObservedValue.Constructed record)
                    || !(step instanceof TermPath.Step.Field(String name))) {
                return null;
            }
            at = record.field(name);
        }
        Place place = at == null ? null : carrier.placeOf(at);
        if (!(place instanceof Count count)) {
            return null;
        }
        ExactRatio exactly = count.exactly();
        return exactly.isWhole() && exactly.floor() instanceof ExactAnswer.Held<BigInteger>(
                BigInteger whole) ? whole : null;
    }

    /** {@code element} holding {@code value} {@code steps} inside it, or null where it has no
     *  such place. */
    private static ObservedValue placedAt(ObservedValue element, List<TermPath.Step> steps,
                                          ObservedValue value) {
        if (steps.isEmpty()) {
            return value;
        }
        if (!(element instanceof ObservedValue.Constructed(TypeSymbol type,
                Map<String, ObservedValue> fields))
                || !(steps.getFirst() instanceof TermPath.Step.Field(String name))
                || !fields.containsKey(name)) {
            return null;
        }
        ObservedValue inner = placedAt(fields.get(name), steps.subList(1, steps.size()), value);
        if (inner == null) {
            return null;
        }
        Map<String, ObservedValue> moved = new LinkedHashMap<>(fields);
        moved.put(name, inner);
        return new ObservedValue.Constructed(type, moved);
    }

    /**
     * A group of elements read inside a container coming to the numbers fixed: its own places are
     * the group's, and the container and what its elements come to are the whole's. Each element
     * walked to is read the same way, so a statement about one of them that reads the container
     * reads the whole.
     */
    private record InsideTheWhole(BorderQuantity.Observation group,
                                  BorderQuantity.Observation whole, TermPath container)
            implements BorderQuantity.Observation {

        private boolean ofTheWhole(TermPath path) {
            return path.isAtOrUnder(container) && !path.isAtOrUnder(container.element());
        }

        @Override
        public WalkResult<ObservationAtPoint> at(TermPath path) {
            return ofTheWhole(path) ? whole.at(path) : group.at(path);
        }

        @Override
        public WalkResult<List<ObservedValue>> everyValueAt(TermPath path) {
            return path.isAtOrUnder(container.element()) ? whole.everyValueAt(path)
                    : group.everyValueAt(path);
        }

        @Override
        public WalkResult<List<BorderQuantity.Observation>> eachElementOf(TermPath of) {
            WalkResult<List<BorderQuantity.Observation>> elements = group.eachElementOf(of);
            if (!of.equals(container)
                    || !(elements instanceof WalkResult.Reached<List<BorderQuantity.Observation>>(
                            var each))) {
                return elements;
            }
            List<BorderQuantity.Observation> out = new ArrayList<>();
            for (BorderQuantity.Observation one : each) {
                out.add(new InsideTheWhole(one, whole, container));
            }
            return WalkResult.reached(out);
        }

        @Override
        public BorderQuantity.Lastness lastToHold(TermPath of, TermPath position) {
            return group.lastToHold(of, position);
        }

        @Override
        public WalkResult<BorderQuantity.Among> among(TermPath of) {
            return group.among(of);
        }

        @Override
        public WalkResult<List<BorderQuantity.AnElement>> elementsOf(TermPath of) {
            WalkResult<List<BorderQuantity.AnElement>> elements = group.elementsOf(of);
            if (!of.equals(container)
                    || !(elements instanceof WalkResult.Reached<List<BorderQuantity.AnElement>>(
                            var each))) {
                return elements;
            }
            List<BorderQuantity.AnElement> out = new ArrayList<>();
            for (BorderQuantity.AnElement one : each) {
                out.add(new BorderQuantity.AnElement(one.element(),
                        new InsideTheWhole(one.reading(), whole, container)));
            }
            return WalkResult.reached(out);
        }

        @Override
        public boolean choseAnElement() {
            return group.choseAnElement();
        }

        /**
         * A run over the container — what its elements come to at a place, or what is computed of
         * each — is the whole's; anything else read once for the row is read of this reading.
         */
        @Override
        public <T> T keptOf(BorderQuantity.ReadAlike<T> asked) {
            return asked instanceof WhatATermRead.ARun
                    || asked instanceof WhatATermRead.ARunOfEachElement
                    ? whole.keptOf(asked) : asked.readAt(this);
        }
    }
}
