package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.check.DeclaredBounds;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.TypeView;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Rel;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.TypeSymbol;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.EnumSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
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
 * <p><b>An element read with those numbers where they are fixed.</b> A row holding the elements of
 * a group alone comes to what they come to, which is not the number fixed. So the group is read
 * with its own places answered by the row holding it and every number of the whole answered as
 * fixed ({@link Fixed#beside}, read through {@link BorderQuantity.Observation#fixedAt}): what it
 * answers in any container coming to them.
 *
 * <p><b>Then the elements are moved to come to it.</b> The elements a sharing draws are the values
 * they were listed at, and a total of them is whatever those come to. Each is moved at every place
 * a total adds up, once for each place to the one number every total of it asks, inside the run of
 * that place its answers hold over — between the numbers that place turns over at — until the
 * elements come to what was fixed ({@link Fixed#spread}). What comes of that is read back against
 * every total fixed, and read again whole before it is offered, as every container is.
 */
final class ContainerAsAWhole {

    /** The most values of each run between the turns a total nothing asks is tried at. */
    private static final int MOST_VALUES_OF_EACH_RUN =
            CompositionBudget.TOTALS_A_COUNT_IS_TRIED_AT.maximum();

    private static final int MOST_ELEMENTS =
            CompositionBudget.ELEMENTS_A_COUNT_IS_COMPOSED_WITH.maximum();

    /**
     * A total the row asks of the container, and the numbers it is tried at.
     *
     * @param term  the total
     * @param asked the numbers the demand on it leaves: what a container composed comes to is one
     *              of them, the container of none's nought among them. Which of them are tried is
     *              chosen where every number of the whole is ({@link ContainerAsAWhole#of})
     * @param named the number the demand names, where it names one
     * @param adds  the orders the total is measured on
     */
    record ATotal(NumericTerm term, NumericSet asked, Place named, TermOrders adds) {

        ATotal {
            Objects.requireNonNull(term, "a total is a number");
            Objects.requireNonNull(asked, "asked to be some numbers");
            Objects.requireNonNull(adds, "on some order");
            Objects.requireNonNull(adds.answered(), "that answers a number");
        }

        /** The order the total's numbers are answered on. */
        Carrier on() {
            return adds.answered();
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
    /** What the row asks the container to come to, which the container of none is held to as
     *  every container is. */
    private final List<ATotal> asked;
    /** The number the rules count the container by, or null where nothing counts it
     *  ({@link ContainersAddingUp#countTaken}). */
    private final NumericTerm.FromOnePosition counted;
    /** Whether a statement reads how many the container holds, which then stands beside an
     *  element as the totals do. */
    private final boolean sizeIsRead;

    private ContainerAsAWhole(TermPath container, List<OneNumber> numbers, List<ATotal> asked,
                              NumericTerm.FromOnePosition counted, boolean sizeIsRead) {
        this.container = container;
        this.numbers = List.copyOf(numbers);
        this.asked = List.copyOf(asked);
        this.counted = counted;
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
     * <p>A total the statements read and the row does not ask is tried where they turn over on it,
     * inside what the region leaves it ({@link #turningOn}), the elements being moved to come to
     * it; {@code beside} is where the numbers beside the elements are fixed, which those turns
     * read. How
     * many the container holds is fixed where a statement reads it, or where a total is of a form
     * of its elements' numbers, which comes to so much more for each element it holds; it is tried
     * at what the rules and the region leave it ({@link ContainersAddingUp#howMany}) and the row
     * asks of it ({@code size}). Both are asked of the owner every other search asks, so a number
     * the rules refuse is never one a container is composed to come to.
     */
    static ContainerAsAWhole of(TermPath container, TypeView view,
                                List<CardinalityComposer.Asked> asked, List<ATotal> totals,
                                Map<NumericTerm, Place> beside, NumericSet size,
                                Quantities measuring, SearchRegion within,
                                RuleReadingContext reading) {
        Map<NumericTerm, OneNumber> out = new LinkedHashMap<>();
        boolean howManyIsRead = false;
        NumericTerm.FromOnePosition counted = ContainersAddingUp.countTaken(view, container,
                reading);
        SearchRegion composable = composableIn(view, container, within, reading);
        for (ATotal each : totals) {
            NumbersOfTheWhole.AddedUp added = NumbersOfTheWhole.addedUp(each.term());
            Carrier carrier = carrierAt(added, measuring);
            if (added == null || carrier == null) {
                return null;
            }
            out.put(each.term(), new OneNumber(each.term(), added, carrier,
                    TermRealizations.onTheOrder(each.asked(), each.adds(), each.named(),
                            composable, UsualPlaces.of(each.adds().term(), each.on(),
                                    reading.today()))));
        }
        NumericTerm many = null;
        for (CardinalityComposer.Asked each : asked) {
            if (!(each instanceof CardinalityComposer.Asked.SoManyMeeting meeting)) {
                continue;
            }
            for (NumericTerm term : meeting.perElement().numbers()) {
                if (!NumbersOfTheWhole.ofTheWhole(term, container)) {
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
                TermRealizations.Tried left = carrier == null ? null
                        : turningOn(term, asked, beside, measuring, composable, reading);
                if (left == null) {
                    return null;
                }
                out.put(term, new OneNumber(term, added, carrier, left));
            }
        }
        boolean formed = out.values().stream().anyMatch(each ->
                !each.added().weight().equals(ExactRatio.ONE) || !each.added().constant().isZero());
        if (howManyIsRead || formed) {
            NumericTerm holds = many != null ? many : new NumericTerm.ValueOf(container);
            out.put(holds, new OneNumber(holds, null, null, sizes(
                    ContainersAddingUp.howMany(view, container, within, reading, null), size)));
        }
        return new ContainerAsAWhole(container, new ArrayList<>(out.values()), totals, counted,
                howManyIsRead);
    }

    /**
     * The region the numbers of {@code container} as a whole are chosen in: {@code within}, with
     * the container holding no more elements than a count composes one with.
     *
     * <p>Every number of the whole is chosen here — a total the row asks ({@link ATotal}) and one
     * the statements only read ({@link #turningOn}). Where a rule relates a total to how many
     * elements add up to it, the region asked of every size leaves a total no container composed
     * here comes to, and a total chosen there is one no elements are drawn for. The region as it
     * is where nothing counts the container, or it cannot carry the bound.
     */
    private static SearchRegion composableIn(TypeView view, TermPath container,
                                             SearchRegion within, RuleReadingContext reading) {
        NumericTerm.FromOnePosition counted =
                ContainersAddingUp.countTaken(view, container, reading);
        return counted != null && within.assuming(new LinearForm<>(
                        ExactRatio.of(-MOST_ELEMENTS), Map.of(counted, ExactRatio.ONE)), Rel.LE)
                instanceof SearchRegion.Assumption.Taken(SearchRegion taken) ? taken : within;
    }

    /**
     * The numbers a total nothing asks of is tried at: where the statements turn over on it, with
     * the numbers beside the elements where {@code beside} fixes them, and values inside each run
     * between — all of them inside what the region leaves it. A statement whose turn reads an
     * element as well turns nowhere the total alone says, and adds no place. Nowhere where the
     * region leaves the total nowhere: the container of none is no choice of these, and is looked
     * at apart from them ({@link CardinalityComposer}).
     */
    private static TermRealizations.Tried turningOn(NumericTerm term,
                                                    List<CardinalityComposer.Asked> asked,
                                                    Map<NumericTerm, Place> beside,
                                                    Quantities measuring, SearchRegion within,
                                                    RuleReadingContext reading) {
        TermOrders orders = measuring.ordersOf(term);
        Carrier carrier = orders == null ? null : orders.answered();
        if (carrier == null) {
            return null;
        }
        Set<CompositionRepertoire> unnamed = EnumSet.noneOf(CompositionRepertoire.class);
        NumericDomain.Bounds run = switch (within.projectionOf(term)) {
            case NumericDomain.FormProjection.Within(NumericDomain.Bounds held) ->
                    held == null ? NumericDomain.Bounds.OPEN : held;
            case NumericDomain.FormProjection.NothingIsLeft _ -> null;
            case null -> NumericDomain.Bounds.OPEN;
        };
        if (run == null) {
            return new TermRealizations.Tried(List.of(),
                    new TermRealizations.Remainder.Exhausted());
        }
        List<ExactRatio> turns = new ArrayList<>();
        // As many values of each run as an element of whole numbers needs for every remainder of
        // the total a statement puts it on the line at ({@link AStatementAtARow#remaindersOf}),
        // up to the figure.
        int remainders = 1;
        for (CardinalityComposer.Asked one : asked) {
            List<ExactRatio> where = one.turnsAt(term, beside);
            if (where != null) {
                turns.addAll(where);
            }
            remainders = Math.max(remainders, one.remaindersOf(term));
        }
        Set<CompositionCapacity> unheld = new LinkedHashSet<>();
        List<Place> places = CardinalityComposer.valuesAlong(carrier, run, turns,
                Math.min(remainders, MOST_VALUES_OF_EACH_RUN),
                UsualPlaces.of(term, carrier, reading.today()), unheld, unnamed);
        TermRealizations.Remainder rest = unnamed.isEmpty()
                ? new TermRealizations.Remainder.StoppedAt(
                        CompositionBudget.TOTALS_A_COUNT_IS_TRIED_AT)
                : new TermRealizations.Remainder.SomeOf(unnamed);
        // A place a statement turns at that this could not write is a total not tried for want of
        // a number, which is said as that and not as the figure.
        return new TermRealizations.Tried(places, unheld.isEmpty() ? rest
                : new TermRealizations.Remainder.NotHeld(unheld, rest));
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

    /**
     * How many the container may hold: what {@code left} leaves, of the counts the row asks for
     * where it asks ({@code size}), from one up to the most a count composes it with. Nothing where
     * the rules leave no count at all; stopped at that most where they leave more. Not none: the
     * container of none is looked at apart from every choice of the whole
     * ({@link CardinalityComposer}).
     */
    private static TermRealizations.Tried sizes(DeclaredBounds.CountRange left, NumericSet size) {
        if (left == null || left.empty()) {
            return new TermRealizations.Tried(List.of(),
                    new TermRealizations.Remainder.Exhausted());
        }
        List<Place> out = new ArrayList<>();
        for (int many = Math.max(1, left.least()); many <= Math.min(left.most(), MOST_ELEMENTS);
                many++) {
            if (size == null || size.holds(Count.of(many), Carrier.WHOLE)) {
                out.add(Count.of(many));
            }
        }
        return new TermRealizations.Tried(out, left.most() > MOST_ELEMENTS
                ? new TermRealizations.Remainder.StoppedAt(
                        CompositionBudget.ELEMENTS_A_COUNT_IS_COMPOSED_WITH)
                : new TermRealizations.Remainder.Exhausted());
    }

    /**
     * Whether the container of none is one the row and the region leave: every total the row asks
     * holds nought, which is what adding up nothing comes to; and the region leaves how many it
     * holds at nought and every total of the whole at nought.
     *
     * <p>Three answers of the region kept three. Where fixing those is what shows the region
     * leaves nothing, the rules refuse the container of none and it is no container. Where the
     * region was shown to leave nothing before anything was fixed, it says nothing of the
     * container of none — an element held to a number no element can be leaves every row of an
     * element nothing, and the container of none holds no element — so it is still one, and the
     * row written of it is read against the rules where every row is. And where neither, it is
     * one.
     */
    boolean admitsNone(SearchRegion within) {
        for (ATotal each : asked) {
            if (!each.asked().holds(Count.of(0), each.on())) {
                return false;
            }
        }
        Map<NumericTerm, Place> none = new LinkedHashMap<>();
        for (OneNumber one : numbers) {
            if (one.added() != null) {
                none.put(one.term(), Count.of(0));
            }
        }
        return leaves(within, none, 0);
    }

    /**
     * Whether the region leaves something with {@code fixed} standing and the container holding
     * {@code held} elements — true where it was shown to leave nothing before either was fixed,
     * which says nothing of these ({@link #admitsNone}).
     */
    private boolean leaves(SearchRegion within, Map<NumericTerm, Place> fixed, int held) {
        Map<NumericTerm, Place> standing = new LinkedHashMap<>(fixed);
        if (counted != null) {
            standing.put(counted, Count.of(held));
        }
        return standing.isEmpty() || within.emptiness().isPresent()
                || within.given(standing).emptiness().isEmpty();
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

        /**
         * {@code beside} with every number of the whole standing where it is fixed: what a reading
         * of some of the elements answers for them ({@link BorderQuantity.Observation#fixedAt}),
         * so that what a group answers is what it answers in any container coming to them. Read
         * off the group instead, they would be what the group alone comes to.
         */
        Map<NumericTerm, Place> beside(Map<NumericTerm, Place> beside) {
            Map<NumericTerm, Place> out = new LinkedHashMap<>(beside);
            out.putAll(fixed);
            return out;
        }

        /**
         * Whether {@code held} elements can come to every total fixed together: the totals adding
         * up one place each say what the numbers there come to, and where two of them say
         * different things no elements meet both.
         */
        boolean comesTogetherIn(int held) {
            return owedAtEachPlace(held) != null;
        }

        /**
         * Whether the region leaves a container of {@code held} elements coming to these numbers:
         * where a rule relates a total to how many add up to it, a size it refuses is one no
         * elements are drawn for.
         */
        boolean standsIn(SearchRegion within, int held) {
            return leaves(within, fixed, held);
        }

        /**
         * What the numbers at each place a total adds up are to come to across {@code held}
         * elements for every total to stand where it is fixed — one number for each place,
         * whichever totals of it are fixed — or null where some total asks no whole number of
         * them, or two totals of one place ask two.
         */
        private Map<TermPath, Owed> owedAtEachPlace(int held) {
            Map<TermPath, Owed> out = new LinkedHashMap<>();
            for (OneNumber one : numbers) {
                if (one.added() == null) {
                    continue;
                }
                BigInteger target = owed(one, Count.number(fixed.get(one.term())), held);
                if (target == null) {
                    return null;
                }
                Owed had = out.putIfAbsent(one.added().place(),
                        new Owed(one.added().place(), one.carrier(), target));
                if (had != null && !had.target().equals(target)) {
                    return null;
                }
            }
            return out;
        }

        /** Whether {@code elements} come to every total fixed, each worked out of them. */
        private boolean comeToEvery(List<ObservedValue> elements) {
            for (OneNumber one : numbers) {
                if (one.added() == null) {
                    continue;
                }
                List<TermPath.Step> steps = stepsInside(one.added().place());
                BigInteger target = owed(one, Count.number(fixed.get(one.term())),
                        elements.size());
                if (steps == null || target == null) {
                    return false;
                }
                BigInteger sum = BigInteger.ZERO;
                for (ObservedValue each : elements) {
                    BigInteger at = wholeAt(each, steps, one.carrier());
                    if (at == null) {
                        return false;
                    }
                    sum = sum.add(at);
                }
                if (!sum.equals(target)) {
                    return false;
                }
            }
            return true;
        }

        /**
         * {@code drawn} with each element moved at every place a total adds up, inside the run of
         * that place it was listed in, so that the elements come to every total fixed — or null
         * where they do not.
         *
         * <p>Once for each place, to the one number every total of it asks there
         * ({@link #owedAtEachPlace}): moved once for each total, the second of two totals of one
         * place would undo the first. And read back before it is handed over, so what comes back
         * comes to every total fixed or is nothing.
         *
         * <p>An element may start from any value it answers alike to, which {@code alike} lists
         * for it: the values of a group answer every statement the same, and the run one of them
         * stands in may reach where another's does not. Each starts from one whose run goes
         * furthest up, and as many as the total needs from one whose run goes furthest down — the
         * {@code variant}-th of those that go as far, since the values of a group are alike to the
         * statements and not to the type, which may tie a place no statement reads to the number
         * moved.
         *
         * @param alike   for each element drawn, the values it answers alike to, or null where it
         *                is to start from where it was drawn
         * @param variant which of the starts going as far each element takes
         * @param turns  where each place a total adds up turns over, with every number of the
         *               whole standing where it is fixed; null at a place where that could not be
         *               worked out, which leaves the elements where they were listed
         * @param region what the rules leave each such place, null where they leave it nothing
         */
        List<ObservedValue> spread(List<ObservedValue> drawn, List<List<ObservedValue>> alike,
                                   int variant, Function<TermPath, List<ExactRatio>> turns,
                                   Function<TermPath, NumericDomain.Bounds> region) {
            List<ObservedValue> out = new ArrayList<>(drawn);
            Map<TermPath, Owed> owed = owedAtEachPlace(out.size());
            if (owed == null) {
                return null;
            }
            // The places already moved, which a start taken at a later place keeps where they
            // were moved to: a value an element answers alike to is one start, and taken whole at
            // the second place it would put the first place back where it was listed.
            List<List<TermPath.Step>> moved = new ArrayList<>();
            for (Owed one : owed.values()) {
                List<TermPath.Step> steps = stepsInside(one.place());
                NumericDomain.Bounds leftByTheRegion = region.apply(one.place());
                if (steps == null || leftByTheRegion == null) {
                    return null;
                }
                BigInteger target = one.target();
                List<ExactRatio> where = turns.apply(one.place());
                WholeNumbersLeft left = WholeNumbersLeft.of(leftByTheRegion);
                List<List<Start>> startsOf = new ArrayList<>();
                for (int each = 0; each < out.size(); each++) {
                    List<Start> starts = new ArrayList<>();
                    for (ObservedValue listed : alike == null || alike.get(each) == null
                            ? List.of(out.get(each)) : alike.get(each)) {
                        ObservedValue start = listed;
                        for (List<TermPath.Step> before : moved) {
                            ObservedValue there = valueAt(out.get(each), before);
                            start = start == null || there == null ? null
                                    : placedAt(start, before, there);
                        }
                        if (start == null) {
                            continue;
                        }
                        BigInteger value = wholeAt(start, steps, one.carrier());
                        if (value != null) {
                            starts.add(new Start(start, value, where == null
                                    ? new BigInteger[] {value, value}
                                    : runOf(value, where, left)));
                        }
                    }
                    if (starts.isEmpty()) {
                        return null;
                    }
                    startsOf.add(starts);
                }
                // Each element from a start whose run reaches furthest up, and then, element by
                // element while the least they can come to is still above the total, from one
                // reaching furthest down. Which way the total is owed is asked of the starts
                // taken: asked of the values drawn, it is a way a start taken after may reverse.
                Start[] taken = new Start[out.size()];
                for (int each = 0; each < taken.length; each++) {
                    taken[each] = furthest(startsOf.get(each), 1, variant);
                }
                for (int each = 0; each < taken.length && aboveIt(least(taken), target); each++) {
                    taken[each] = furthest(startsOf.get(each), -1, variant);
                }
                BigInteger[] at = new BigInteger[taken.length];
                BigInteger delta = target;
                for (int each = 0; each < taken.length; each++) {
                    out.set(each, taken[each].value());
                    at[each] = taken[each].at();
                    delta = delta.subtract(at[each]);
                }
                for (int each = 0; each < at.length && delta.signum() != 0; each++) {
                    BigInteger edge = taken[each].run()[delta.signum() > 0 ? 1 : 0];
                    BigInteger reach = edge == null ? delta : edge.subtract(at[each]);
                    BigInteger step = delta.signum() > 0 ? delta.min(reach) : delta.max(reach);
                    at[each] = at[each].add(step);
                    delta = delta.subtract(step);
                }
                if (delta.signum() != 0) {
                    return null;
                }
                for (int each = 0; each < at.length; each++) {
                    ObservedValue shifted = placedAt(out.get(each), steps,
                            one.carrier().valueOf(Count.of(new BigDecimal(at[each]))));
                    if (shifted == null) {
                        return null;
                    }
                    out.set(each, shifted);
                }
                moved.add(steps);
            }
            return comeToEvery(out) ? out : null;
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

    /** What the numbers at {@code place}, written on {@code carrier}, are to come to across the
     *  elements. */
    private record Owed(TermPath place, Carrier carrier, BigInteger target) {}

    /** A value an element may start from, the whole number it holds where it is moved, and the
     *  run it may be moved inside. */
    private record Start(ObservedValue value, BigInteger at, BigInteger[] run) {}

    /** The {@code variant}-th of the starts whose run reaches furthest {@code way}. */
    private static Start furthest(List<Start> starts, int way, int variant) {
        List<Start> out = new ArrayList<>();
        for (Start each : starts) {
            if (out.isEmpty() || further(each.run(), out.getFirst().run(), way)) {
                out.clear();
                out.add(each);
            } else if (!further(out.getFirst().run(), each.run(), way)) {
                out.add(each);
            }
        }
        return out.get(variant % out.size());
    }

    /** The least the elements from {@code taken} can come to, or null where some run is open
     *  below. */
    private static BigInteger least(Start[] taken) {
        BigInteger out = BigInteger.ZERO;
        for (Start each : taken) {
            if (each.run()[0] == null) {
                return null;
            }
            out = out.add(each.run()[0]);
        }
        return out;
    }

    /** Whether {@code least} is above {@code target}; an open end is no end above it. */
    private static boolean aboveIt(BigInteger least, BigInteger target) {
        return least != null && least.compareTo(target) > 0;
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

    /** What {@code element} holds {@code steps} inside it, or null where it holds nothing there. */
    private static ObservedValue valueAt(ObservedValue element, List<TermPath.Step> steps) {
        ObservedValue at = element;
        for (TermPath.Step step : steps) {
            if (!(at instanceof ObservedValue.Constructed record)
                    || !(step instanceof TermPath.Step.Field(String name))) {
                return null;
            }
            at = record.field(name);
        }
        return at;
    }

    /** The whole number {@code element} holds {@code steps} inside it, or null where it holds none
     *  there. */
    private static BigInteger wholeAt(ObservedValue element, List<TermPath.Step> steps,
                                      Carrier carrier) {
        ObservedValue at = valueAt(element, steps);
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

}
