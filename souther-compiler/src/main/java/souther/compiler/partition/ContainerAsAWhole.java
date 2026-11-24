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
import java.util.Arrays;
import java.util.Comparator;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.HashSet;
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
 * that place it answers alike over and the region leaves it, its other numbers held to the runs
 * they answer alike over and moved with it where a rule ties them to it ({@link Sized#spread}).
 * Which values reach the number is worked out exactly over those runs, so a total the elements can
 * come to is one they are moved to.
 *
 * <p><b>And asked of the region before it is offered.</b> A container is the region's to admit,
 * the container of none as much as any: with how many it holds and every number of the whole
 * standing, the region is asked of each element ({@link Sized#admits}), and what it refuses —
 * a class, a hole, a rule tying one field of an element to another or to a total — is no
 * container offered. Read again whole before it is offered, as every container is.
 */
final class ContainerAsAWhole {

    /** The most values of each run between the turns a total nothing asks is tried at. */
    private static final int MOST_VALUES_OF_EACH_RUN =
            CompositionBudget.TOTALS_A_COUNT_IS_TRIED_AT.maximum();

    private static final int MOST_ELEMENTS =
            CompositionBudget.ELEMENTS_A_COUNT_IS_COMPOSED_WITH.maximum();

    private static final int MOST_RUNS =
            CompositionBudget.RUNS_A_COUNTS_ELEMENTS_CAN_COME_TO.maximum();

    private static final int MOST_VALUES_MOVED_TO =
            CompositionBudget.VALUES_AN_ELEMENT_IS_MOVED_TO_TRIED.maximum();

    /** How many more values the elements of one container may be tried moved to, and whether
     *  the figure left some untried. */
    private static final class Tries {

        private int left;
        private boolean cut;

        private Tries(int left) {
            this.left = left;
        }
    }

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
    /** The orders the numbers inside an element are written on, which an element is asked of the
     *  region at. */
    private final Quantities measuring;
    /** Whether holding the container to the most elements a count composes one with took a
     *  number away from one of the numbers of the whole: a number left only to a larger
     *  container is one the figure stopped, and not one the model refuses. */
    private final boolean cutByTheFigure;

    private ContainerAsAWhole(TermPath container, List<OneNumber> numbers, List<ATotal> asked,
                              NumericTerm.FromOnePosition counted, boolean sizeIsRead,
                              Quantities measuring, boolean cutByTheFigure) {
        this.container = container;
        this.numbers = List.copyOf(numbers);
        this.asked = List.copyOf(asked);
        this.counted = counted;
        this.sizeIsRead = sizeIsRead;
        this.measuring = measuring;
        this.cutByTheFigure = cutByTheFigure;
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
        boolean cut = false;
        if (composable != within) {
            for (NumericTerm each : out.keySet()) {
                cut |= !Objects.equals(within.projectionOf(each), composable.projectionOf(each));
            }
        }
        return new ContainerAsAWhole(container, new ArrayList<>(out.values()), totals, counted,
                howManyIsRead, measuring, cut);
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
     * at apart from them ({@link #ofNone}).
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
     * container of none is looked at apart from every choice of the whole ({@link #ofNone}).
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
     * Every choice of a number for each number of the whole, up to the figure the choices of
     * several totals are held to, and why there are no more — with the most elements a count
     * composes a container with among them where holding the container to it took a number away
     * ({@link #composableIn}).
     */
    TermRealizations.Together choices() {
        List<TermRealizations.Tried> each = new ArrayList<>();
        for (OneNumber one : numbers) {
            each.add(one.tried());
        }
        TermRealizations.Together out = TermRealizations.Together.of(each);
        if (!cutByTheFigure) {
            return out;
        }
        return new TermRealizations.Together(out.each(), out.rest().and(CompositionShortfall.of(
                Set.of(CompositionBudget.ELEMENTS_A_COUNT_IS_COMPOSED_WITH))));
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
     * The numbers of the whole the container of none comes to — nought for every total, which is
     * what adding up nothing comes to, and none held — or null where the row asks a total that
     * nought is not.
     *
     * <p>Apart from {@link #choices}: no element is drawn for it, so no number of the whole is
     * chosen for one to answer by, and what it comes to is read off it. Whether the region leaves
     * it is asked as of every container ({@link Sized#admits}).
     */
    Fixed ofNone() {
        for (ATotal each : asked) {
            if (!each.asked().holds(Count.of(0), each.on())) {
                return null;
            }
        }
        Map<NumericTerm, Place> fixed = new LinkedHashMap<>();
        for (OneNumber one : numbers) {
            if (one.added() != null || sizeIsRead) {
                fixed.put(one.term(), Count.of(0));
            }
        }
        return new Fixed(fixed, 0);
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

        /** Whether a total is fixed, which the elements are then moved to come to. */
        boolean movesTheElements() {
            return numbers.stream().anyMatch(one -> one.added() != null);
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
         * A container of {@code held} elements coming to these numbers, in {@code within}: the
         * region with how many it holds and every number fixed standing, which the elements are
         * moved in and each container is asked of.
         */
        Sized holding(SearchRegion within, int held) {
            Map<NumericTerm, Place> standing = new LinkedHashMap<>(fixed);
            if (counted != null) {
                standing.put(counted, Count.of(held));
            }
            return new Sized(this, standing.isEmpty() ? within : within.given(standing), held);
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
     * A container of so many elements coming to the numbers of one {@link Fixed}, and the region
     * with those standing: what the elements are moved in, and what every container of them is
     * asked of before it is offered.
     */
    final class Sized {

        private final Fixed fixed;
        private final SearchRegion region;
        private final int held;
        /** What the region answers of each element, kept for the containers that hold it again. */
        private final Map<ObservedValue, Boolean> admitted = new HashMap<>();

        private Sized(Fixed fixed, SearchRegion region, int held) {
            this.fixed = fixed;
            this.region = region;
            this.held = held;
        }

        /** Whether the region leaves a container of so many coming to these numbers: where a rule
         *  relates a total to how many add up to it, a size it refuses is one no elements are
         *  drawn for. */
        boolean leavesSomething() {
            return region.emptiness().isEmpty();
        }

        /**
         * Whether {@code elements} are a container the row and the region leave: as many as this
         * holds, coming to every total fixed, each element one the region leaves with its numbers
         * standing beside these, and no two alike at a place {@code apart} keeps them apart at.
         *
         * <p>The one question every container is offered on, the container of none's included —
         * what any reading on the way did not see, a class or a hole or a rule tying a number of
         * an element to another, the region answers here.
         *
         * @param parts where inside an element the numbers the region is asked at stand
         * @param apart the fields the elements are kept apart at, the whole element for a set
         */
        boolean admits(List<ObservedValue> elements, List<TermPath> parts,
                       List<List<String>> apart) {
            if (elements.size() != held || !fixed.comeToEvery(elements) || !leavesSomething()) {
                return false;
            }
            for (ObservedValue each : elements) {
                Boolean left = admitted.get(each);
                if (left == null) {
                    left = region.given(numbersOf(each, parts, null)).emptiness().isEmpty();
                    admitted.put(each, left);
                }
                if (!left) {
                    return false;
                }
            }
            return keptApart(elements, apart);
        }

        /**
         * {@code drawn} with each element moved at every place a total adds up, so that the
         * elements come to every total fixed — or null where no values of the runs they are moved
         * in come to it.
         *
         * <p>Once for each place, to the one number every total of it asks there
         * ({@link Fixed#owedAtEachPlace}): moved once for each total, the second of two totals of
         * one place would undo the first.
         *
         * <p>An element may start from any value it answers alike to, which {@code alike} lists
         * for it: the values of a group answer every statement the same, and the run one of them
         * stands in may reach where another's does not. Each start is moved inside the run of the
         * place it answers alike over and the region leaves it, with its other numbers held to
         * theirs ({@link #optionOf}). What the elements can come to over all of those is worked
         * out run by run ({@link #reachOf}), and the elements are moved from the last back to come
         * to the number owed, each to the value of its run nearest where it started that leaves the
         * ones before it a number they can come to, and what a rule ties to it moved with it.
         * {@code variant} is which start an element tries first, since the values of a group are
         * alike to the statements and not to everything the region knows of them.
         *
         * @param alike   for each element drawn, the values it answers alike to, or null where it
         *                is to start from where it was drawn
         * @param turns   where each place a total adds up turns over, with every number of the
         *                whole standing where it is fixed; null at a place where that could not be
         *                worked out, which leaves the elements where they were listed
         * @param parts   where inside an element the numbers the region is asked at stand
         * @param apart   the fields the elements are kept apart at, the whole element for a set,
         *                which no element is moved to hold what another holds at
         */
        List<ObservedValue> spread(List<ObservedValue> drawn, List<List<ObservedValue>> alike,
                                   int variant, Function<TermPath, List<ExactRatio>> turns,
                                   List<TermPath> parts, List<List<String>> apart,
                                   Set<CompositionBudget> refused,
                                   Set<CompositionRepertoire> unnamed) {
            List<ObservedValue> out = new ArrayList<>(drawn);
            Map<TermPath, Owed> owed = fixed.owedAtEachPlace(out.size());
            if (owed == null) {
                return null;
            }
            // The places already moved, which a start taken at a later place keeps where they
            // were moved to: a value an element answers alike to is one start, and taken whole at
            // the second place it would put the first place back where it was listed.
            List<TermPath> moved = new ArrayList<>();
            for (Owed one : owed.values()) {
                List<TermPath.Step> steps = stepsInside(one.place());
                if (steps == null) {
                    return null;
                }
                List<List<Option>> options = new ArrayList<>();
                for (int each = 0; each < out.size(); each++) {
                    List<Option> of = new ArrayList<>();
                    for (ObservedValue listed : alike == null || alike.get(each) == null
                            ? List.of(out.get(each)) : alike.get(each)) {
                        ObservedValue start = listed;
                        for (TermPath before : moved) {
                            List<TermPath.Step> there = stepsInside(before);
                            ObservedValue held = valueAt(out.get(each), there);
                            start = start == null || held == null ? null
                                    : placedAt(start, there, held);
                        }
                        Option option = start == null ? null
                                : optionOf(start, one, steps, turns, parts, moved);
                        if (option != null) {
                            of.add(option);
                        }
                    }
                    if (of.isEmpty()) {
                        return null;
                    }
                    options.add(of);
                }
                List<List<Span>> reach = reachOf(options);
                if (reach == null) {
                    refused.add(CompositionBudget.RUNS_A_COUNTS_ELEMENTS_CAN_COME_TO);
                    return null;
                }
                if (!Span.anyHolds(reach.getLast(), one.target())) {
                    return null;
                }
                ObservedValue[] placed = new ObservedValue[out.size()];
                Tries tries = new Tries(MOST_VALUES_MOVED_TO * (out.size() + 1));
                // The runs said the number is reached, and only what they do not know of — a
                // hole, a class, a number the region ties to it left none, an element kept apart
                // from another — turns every value away: some of the ways were walked, or the
                // figure stopped the walk.
                if (!placing(out.size() - 1, one.target(), options, reach, variant, one, turns,
                        parts, moved, apart, placed, tries)) {
                    if (tries.cut) {
                        refused.add(CompositionBudget.VALUES_AN_ELEMENT_IS_MOVED_TO_TRIED);
                    } else {
                        unnamed.add(CompositionRepertoire.ELEMENTS_CHOSEN_FOR_A_COUNT);
                    }
                    return null;
                }
                out = new ArrayList<>(Arrays.asList(placed));
                moved.add(one.place());
            }
            return out;
        }

        /**
         * {@code start} as an element moved at the place {@code one} adds up: the whole number it
         * holds there, the run it may be moved in, and the region it is moved in.
         *
         * <p>Every number of an element answers every statement alike inside the run between the
         * nearest numbers its place turns over at, so each of them may be moved inside its own run
         * and the element answers as it did ({@link ContainerAsAWhole#runsOf}). The region is
         * asked of the element with each held to its run and the rest standing — what it holds
         * elsewhere, and the places already moved — and the run of the place moved is what the
         * region leaves it there, inside its own. A number a rule ties to the one moved is moved
         * with it ({@link #realized}). Null where the region leaves the place nothing so, which is
         * no start.
         */
        private Option optionOf(ObservedValue start, Owed one, List<TermPath.Step> steps,
                                Function<TermPath, List<ExactRatio>> turns, List<TermPath> parts,
                                List<TermPath> moved) {
            BigInteger at = wholeAt(start, steps, one.carrier());
            if (at == null) {
                return null;
            }
            SearchRegion around = heldToItsRuns(start, one.place(), turns, parts, moved);
            if (around == null) {
                return null;
            }
            WholeNumbersLeft left = leftAt(around, one.place());
            if (left == WholeNumbersLeft.NONE) {
                return null;
            }
            List<ExactRatio> where = turns.apply(one.place());
            // An end no whole number is read at leaves the element where it is.
            Span run = where == null || left == null ? new Span(at, at) : runOf(at, where, left);
            return run.isEmpty() ? null : new Option(start, at, run, around);
        }

        /**
         * The region with {@code start} in it: each whole number of it but the one at
         * {@code place} held to the run it answers alike over, and every other number, and the
         * places already {@code moved}, standing — or null where the region leaves that nothing.
         */
        private SearchRegion heldToItsRuns(ObservedValue start, TermPath place,
                                           Function<TermPath, List<ExactRatio>> turns,
                                           List<TermPath> parts, List<TermPath> moved) {
            Map<NumericTerm, Place> standing = new LinkedHashMap<>();
            Map<NumericTerm.ValueOf, Span> runs = new LinkedHashMap<>();
            for (TermPath part : parts) {
                if (part.equals(place)) {
                    continue;
                }
                Span run = moved.contains(part) ? null : runsOf(start, part, turns);
                if (run == null) {
                    standing.putAll(numbersOf(start, List.of(part), null));
                } else {
                    runs.put(new NumericTerm.ValueOf(part), run);
                }
            }
            SearchRegion out = standing.isEmpty() ? region : region.given(standing);
            for (Map.Entry<NumericTerm.ValueOf, Span> each : runs.entrySet()) {
                out = within(out, each.getKey(), each.getValue());
            }
            return out.emptiness().isPresent() ? null : out;
        }

        /**
         * The start of {@code option} with the number at {@code one}'s place moved to {@code to},
         * and each other whole number of it held to its run moved, where a rule ties it to that
         * one, to the value nearest where it was that the region leaves it with the ones before it
         * standing — or null where the region leaves one of them none.
         */
        private ObservedValue realized(Option option, BigInteger to, Owed one,
                                       Function<TermPath, List<ExactRatio>> turns,
                                       List<TermPath> parts, List<TermPath> moved, Tries tries) {
            ObservedValue out = placedAt(option.start(), stepsInside(one.place()),
                    one.carrier().valueOf(Count.of(new BigDecimal(to))));
            SearchRegion here = option.around().given(new NumericTerm.ValueOf(one.place()),
                    Count.of(new BigDecimal(to)));
            for (TermPath part : parts) {
                if (out == null) {
                    return null;
                }
                Span run = part.equals(one.place()) || moved.contains(part) ? null
                        : runsOf(out, part, turns);
                if (run == null) {
                    continue;
                }
                NumericTerm.ValueOf term = new NumericTerm.ValueOf(part);
                Carrier carrier = wholeCarrierAt(part);
                BigInteger was = wholeAt(out, stepsInside(part), carrier);
                WholeNumbersLeft left = leftAt(here, part);
                Span span = left == null || left == WholeNumbersLeft.NONE ? null
                        : run.meeting(new Span(left.least(), left.most()));
                BigInteger at = span == null || span.isEmpty() ? null
                        : nearestHeld(span, was, here, term, tries);
                if (at == null) {
                    return null;
                }
                Place placed = Count.of(new BigDecimal(at));
                out = placedAt(out, stepsInside(part), carrier.valueOf(placed));
                here = here.given(term, placed);
            }
            return out;
        }

        /**
         * Whether the elements up to the {@code each}-th can be moved to come to {@code left},
         * each placed in {@code placed} where they can: the {@code each}-th to a value of its run
         * that leaves the rest a number they can come to ({@code reach}), with what a rule ties to
         * that value moved with it ({@link #realized}) and kept apart from the elements after it
         * where {@code apart} keeps them apart — the value nearest where it started first, of the
         * first start from the {@code variant}-th, and the next one where the elements before it
         * cannot then be placed. No more values are tried in all than {@code tries} holds.
         */
        private boolean placing(int each, BigInteger left, List<List<Option>> options,
                                List<List<Span>> reach, int variant, Owed one,
                                Function<TermPath, List<ExactRatio>> turns, List<TermPath> parts,
                                List<TermPath> moved, List<List<String>> apart,
                                ObservedValue[] placed, Tries tries) {
            if (each < 0) {
                return true;
            }
            List<ObservedValue> after = Arrays.asList(placed).subList(each + 1, placed.length);
            List<Option> of = options.get(each);
            NumericTerm.ValueOf term = new NumericTerm.ValueOf(one.place());
            for (int start = 0; start < of.size(); start++) {
                Option option = of.get((start + variant) % of.size());
                for (BigInteger at : candidates(option, reach.get(each), left, term, tries)) {
                    if (tries.left-- <= 0) {
                        tries.cut = true;
                        return false;
                    }
                    ObservedValue element = realized(option, at, one, turns, parts, moved,
                            tries);
                    if (element == null || !keptApartFrom(element, after, apart)) {
                        continue;
                    }
                    placed[each] = element;
                    if (placing(each - 1, left.subtract(at), options, reach, variant, one, turns,
                            parts, moved, apart, placed, tries)) {
                        return true;
                    }
                }
            }
            return false;
        }

        /**
         * The whole numbers of {@code option}'s run that leave {@code left} less them a number the
         * elements before it can come to, and that the region neither holds apart nor puts
         * outside the class of the place: nearest where it started first, and no more of them
         * than the figure ({@link CompositionBudget#VALUES_AN_ELEMENT_IS_MOVED_TO_TRIED}), which
         * {@code tries} is told of where it leaves some out.
         */
        private static List<BigInteger> candidates(Option option, List<Span> before,
                                                   BigInteger left, NumericTerm.ValueOf term,
                                                   Tries tries) {
            List<BigInteger> out = new ArrayList<>();
            for (Span reached : before) {
                Span here = option.run().meeting(reached.subtractedFrom(left));
                if (here.isEmpty()) {
                    continue;
                }
                BigInteger nearest = here.nearest(option.at());
                out.addAll(heldNear(here, nearest, option.around(), term, tries).stream()
                        .filter(at -> !out.contains(at)).toList());
            }
            out.sort(Comparator.comparing(at -> at.subtract(option.at()).abs()));
            if (out.size() > MOST_VALUES_MOVED_TO) {
                tries.cut = true;
            }
            return out.subList(0, Math.min(out.size(), MOST_VALUES_MOVED_TO));
        }

        /**
         * The whole numbers of {@code span} no further from {@code nearest} than the figure that
         * {@code around} neither holds apart nor puts outside the class of the place, nearest
         * first; {@code tries} is told where the span holds more past them.
         */
        private static List<BigInteger> heldNear(Span span, BigInteger nearest,
                                                 SearchRegion around, NumericTerm.ValueOf term,
                                                 Tries tries) {
            List<BigInteger> out = new ArrayList<>();
            for (int step = 0; step <= MOST_VALUES_MOVED_TO; step++) {
                for (BigInteger at : step == 0 ? List.of(nearest) : List.of(
                        nearest.subtract(BigInteger.valueOf(step)),
                        nearest.add(BigInteger.valueOf(step)))) {
                    if (span.holds(at) && heldAt(around, term, at)) {
                        out.add(at);
                    }
                }
            }
            BigInteger past = BigInteger.valueOf(MOST_VALUES_MOVED_TO + 1L);
            if (span.holds(nearest.subtract(past)) || span.holds(nearest.add(past))) {
                tries.cut = true;
            }
            return out;
        }

        /** Whether {@code around} neither holds {@code term} apart from {@code at} nor puts
         *  {@code at} outside its class. */
        private static boolean heldAt(SearchRegion around, NumericTerm.ValueOf term,
                                      BigInteger at) {
            return !around.apartAt(term).has(Count.of(new BigDecimal(at)))
                    && around.classAt(term).holds(at);
        }

        /** The whole number of {@code span} nearest {@code from} that {@code around} neither
         *  holds apart nor puts outside the class of the place, looked for no further than the
         *  figure past the nearest ({@link #heldNear}). */
        private static BigInteger nearestHeld(Span span, BigInteger from, SearchRegion around,
                                              NumericTerm.ValueOf term, Tries tries) {
            List<BigInteger> held = heldNear(span, span.nearest(from), around, term, tries);
            return held.isEmpty() ? null : held.getFirst();
        }

        /**
         * What the first so many of {@code options} can come to, for each count of them from none
         * on, as runs of whole numbers apart from one another — or null where the runs kept would
         * be more than the figure.
         */
        private static List<List<Span>> reachOf(List<List<Option>> options) {
            List<List<Span>> out = new ArrayList<>();
            out.add(List.of(new Span(BigInteger.ZERO, BigInteger.ZERO)));
            for (List<Option> each : options) {
                List<Span> next = new ArrayList<>();
                for (Span had : out.getLast()) {
                    for (Option option : each) {
                        next.add(had.plus(option.run()));
                    }
                }
                List<Span> joined = Span.joined(next);
                if (joined.size() > MOST_RUNS) {
                    return null;
                }
                out.add(joined);
            }
            return out;
        }
    }

    /** What the numbers at {@code place}, written on {@code carrier}, are to come to across the
     *  elements. */
    private record Owed(TermPath place, Carrier carrier, BigInteger target) {}

    /**
     * A value an element may start from, the whole number it holds where it is moved, the run it
     * may be moved in, and the region with its other numbers standing, which says where inside
     * the run it is held apart or of another class.
     */
    private record Option(ObservedValue start, BigInteger at, Span run, SearchRegion around) {}

    /**
     * The whole numbers from {@code low} to {@code high}, either end open where it is null: empty
     * where both are numbers and the first is past the second.
     */
    private record Span(BigInteger low, BigInteger high) {

        /** Lowest first, an open low end before every other. */
        private static final Comparator<Span> BY_LOW = (one, other) -> one.low == null
                ? (other.low == null ? 0 : -1)
                : other.low == null ? 1 : one.low.compareTo(other.low);

        boolean isEmpty() {
            return low != null && high != null && low.compareTo(high) > 0;
        }

        boolean holds(BigInteger at) {
            return (low == null || low.compareTo(at) <= 0) && (high == null || high.compareTo(at) >= 0);
        }

        /** Every sum of a number of this and a number of {@code other}. */
        Span plus(Span other) {
            return new Span(low == null || other.low == null ? null : low.add(other.low),
                    high == null || other.high == null ? null : high.add(other.high));
        }

        /** The numbers {@code from} less a number of this comes to. */
        Span subtractedFrom(BigInteger from) {
            return new Span(high == null ? null : from.subtract(high),
                    low == null ? null : from.subtract(low));
        }

        /** The numbers of both. */
        Span meeting(Span other) {
            BigInteger least = low == null ? other.low
                    : other.low == null ? low : low.max(other.low);
            BigInteger most = high == null ? other.high
                    : other.high == null ? high : high.min(other.high);
            return new Span(least, most);
        }

        /** The number of this nearest {@code at}; not asked of an empty one. */
        BigInteger nearest(BigInteger at) {
            if (low != null && at.compareTo(low) < 0) {
                return low;
            }
            return high != null && at.compareTo(high) > 0 ? high : at;
        }

        /** Whether some span of {@code spans} holds {@code at}. */
        static boolean anyHolds(List<Span> spans, BigInteger at) {
            return spans.stream().anyMatch(each -> each.holds(at));
        }

        /** {@code spans} less the empty ones, those that meet or touch put together, lowest
         *  first. */
        static List<Span> joined(List<Span> spans) {
            List<Span> sorted = new ArrayList<>(spans.stream().filter(each -> !each.isEmpty())
                    .toList());
            sorted.sort(BY_LOW);
            List<Span> out = new ArrayList<>();
            for (Span each : sorted) {
                Span last = out.isEmpty() ? null : out.getLast();
                if (last != null && (last.high == null || each.low == null
                        || each.low.compareTo(last.high.add(BigInteger.ONE)) <= 0)) {
                    out.set(out.size() - 1, new Span(last.low, last.high == null
                            || each.high == null ? null : last.high.max(each.high)));
                } else {
                    out.add(each);
                }
            }
            return out;
        }
    }

    /**
     * The numbers {@code element} holds at {@code parts}, each as the place the region names it
     * at, but the one at {@code except} where that is not null. A part the element holds nothing
     * at, or holds no place of its order at, is left unsaid.
     */
    private Map<NumericTerm, Place> numbersOf(ObservedValue element, List<TermPath> parts,
                                              TermPath except) {
        Map<NumericTerm, Place> out = new LinkedHashMap<>();
        for (TermPath part : parts) {
            List<TermPath.Step> steps = part.equals(except) ? null : stepsInside(part);
            ObservedValue value = steps == null ? null : valueAt(element, steps);
            NumericTerm.ValueOf term = new NumericTerm.ValueOf(part);
            TermOrders orders = value == null ? null : measuring.ordersOf(term);
            Carrier carrier = orders == null ? null : orders.observed();
            Place place = carrier == null ? null : carrier.placeOf(value);
            if (place != null) {
                out.put(term, place);
            }
        }
        return out;
    }

    /**
     * The whole numbers the number {@code element} holds at {@code part} answers every statement
     * alike over — between the nearest numbers {@code turns} says the place turns over at — or
     * null where it is no whole number, or where it turns could not be worked out, which leaves it
     * where it stands.
     */
    private Span runsOf(ObservedValue element, TermPath part,
                        Function<TermPath, List<ExactRatio>> turns) {
        Carrier carrier = wholeCarrierAt(part);
        List<TermPath.Step> steps = carrier == null ? null : stepsInside(part);
        BigInteger at = steps == null ? null : wholeAt(element, steps, carrier);
        List<ExactRatio> where = at == null ? null : turns.apply(part);
        return where == null ? null : runOf(at, where, WholeNumbersLeft.EVERY);
    }

    /** The order the numbers at {@code part} are written on, where it counts in whole numbers. */
    private Carrier wholeCarrierAt(TermPath part) {
        TermOrders orders = measuring.ordersOf(new NumericTerm.ValueOf(part));
        Carrier carrier = orders == null ? null : orders.observed();
        return carrier != null && carrier.countsInWholeNumbers() ? carrier : null;
    }

    /** {@code region} with {@code term} held inside {@code run}; an end the region cannot carry is
     *  left open, which leaves it wider and never narrower than what holds. */
    private static SearchRegion within(SearchRegion region, NumericTerm.ValueOf term, Span run) {
        if (run.low() != null && run.low().equals(run.high())) {
            return region.given(term, Count.of(new BigDecimal(run.low())));
        }
        SearchRegion out = region;
        if (run.low() != null && out.assuming(new LinearForm<>(ExactRatio.of(
                        run.low().negate()), Map.of(term, ExactRatio.ONE)), Rel.GE)
                instanceof SearchRegion.Assumption.Taken(SearchRegion taken)) {
            out = taken;
        }
        if (run.high() != null && out.assuming(new LinearForm<>(ExactRatio.of(
                        run.high().negate()), Map.of(term, ExactRatio.ONE)), Rel.LE)
                instanceof SearchRegion.Assumption.Taken(SearchRegion taken)) {
            out = taken;
        }
        return out;
    }

    /** The whole numbers {@code region} leaves the number at {@code place}: every one where it
     *  says nothing, {@link WholeNumbersLeft#NONE} where it leaves nothing, and null where an end
     *  of what it leaves is no number. */
    private static WholeNumbersLeft leftAt(SearchRegion region, TermPath place) {
        return switch (region.projectionOf(new NumericTerm.ValueOf(place))) {
            case NumericDomain.FormProjection.Within(NumericDomain.Bounds bounds) ->
                    bounds == null ? WholeNumbersLeft.EVERY : WholeNumbersLeft.of(bounds);
            case NumericDomain.FormProjection.NothingIsLeft _ -> WholeNumbersLeft.NONE;
            case null -> WholeNumbersLeft.EVERY;
        };
    }

    /** Whether no two of {@code elements} hold one value at any of the fields of {@code apart}. */
    private static boolean keptApart(List<ObservedValue> elements, List<List<String>> apart) {
        for (List<String> fields : apart) {
            Set<ObservedValue> seen = new HashSet<>();
            for (ObservedValue each : elements) {
                ObservedValue at = atFields(each, fields);
                if (at != null && !seen.add(at)) {
                    return false;
                }
            }
        }
        return true;
    }

    /** Whether {@code element} holds what none of {@code others} holds at each of the fields of
     *  {@code apart}. */
    private static boolean keptApartFrom(ObservedValue element, List<ObservedValue> others,
                                         List<List<String>> apart) {
        for (List<String> fields : apart) {
            ObservedValue at = atFields(element, fields);
            for (ObservedValue other : others) {
                if (at != null && at.equals(atFields(other, fields))) {
                    return false;
                }
            }
        }
        return true;
    }

    /** What {@code element} holds at {@code fields}, or null where it holds nothing there. */
    private static ObservedValue atFields(ObservedValue element, List<String> fields) {
        ObservedValue at = element;
        for (String field : fields) {
            at = at instanceof ObservedValue.Constructed record ? record.field(field) : null;
        }
        return at;
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
     * one, and inside {@code left}.
     */
    private static Span runOf(BigInteger at, List<ExactRatio> turns, WholeNumbersLeft left) {
        ExactRatio here = ExactRatio.of(new BigDecimal(at));
        BigInteger low = left.least();
        BigInteger high = left.most();
        for (ExactRatio turn : turns) {
            int side = turn.compareTo(here);
            if (side == 0) {
                return new Span(at, at);
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
        return new Span(low, high);
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
