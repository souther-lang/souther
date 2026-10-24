package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.Shape;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.Quantity;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LaterNumbersEliminated;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Rel;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Predicate;

/**
 * Containers whose elements meet statements that read, beside the element's own whole number, the
 * total of that number over the container the element is in — so many of them for each.
 *
 * <p><b>Why this is not the elements chosen by what each answers alone.</b> A container of one
 * element comes to that element, so what a row holding it alone answers is not what it answers in
 * a container of others. The total is the container's, and every element's answer turns on it.
 *
 * <p><b>What the total decides.</b> With the total fixed at a whole number, each relation of the
 * statements is a bound on the element's own number alone, so the numbers an element may be while
 * the relations stand as they do are an interval, and the elements of the container are tied
 * together by one thing only: they come to the total. Whether a sharing of the elements out among
 * the ways the relations can stand has a container is therefore exact. The totals it can come to
 * are an interval over the rationals ({@link LaterNumbersEliminated}); at each whole number in it
 * the elements' intervals ({@link WholeNumbersLeft}) are summed, and the total is met where it is
 * between the least and the greatest they come to. The elements are then spread over their
 * intervals to come to it, each to a value of its own.
 *
 * <p><b>Ways the relations can stand.</b> A relation stands as it holds or as it does not; an
 * equality or its denial stands below, at or above nought. A way for each of the relations of all
 * the statements is a cell, and a cell no total and number meet is none. What the statements
 * answer in a cell, which the other positions of the element may change (a truth, a case), is
 * asked of the statements themselves, at a number and a total the cell holds, for each way the
 * element's other positions are listed. A kind of element is a cell and the answers there.
 *
 * <p>Every container is read again as a whole before it is offered, so the cells, which promise
 * what an element answers in the container it was proposed for, are never the answer.
 *
 * <p>Not for a statement that is not forms of the element's number, its total and numbers outside
 * every container against nought ({@link AStatementAtARow#affineRelations}), nor for a carrier
 * that is not whole numbers: those are chosen as they were.
 */
final class CoupledCardinalityComposer {

    private static final ValueName.Stdlib.Operation SUM = ValueName.Stdlib.operation("List", "sum");

    /** The most statements counted together, and the most relations of them whose ways of
     *  standing are taken together. */
    private static final int MOST_STATEMENTS = 3;

    private static final int MOST_RELATIONS = 4;

    private static final int MOST_ELEMENTS =
            CompositionBudget.ELEMENTS_A_COUNT_IS_COMPOSED_WITH.maximum();

    private static final int MOST_OFFERED = CompositionBudget.CONTAINERS_A_COUNT_IS_OFFERED.maximum();

    private static final int MOST_SHARES = CompositionBudget.SHARES_A_COUNT_IS_TRIED_AT.maximum();

    private static final int MOST_TOTALS = CompositionBudget.TOTALS_A_SHARING_IS_TRIED_AT.maximum();

    private static final int MOST_PAIRS =
            CompositionBudget.PAIRS_OF_BOUNDS_A_TOTAL_IS_SOLVED_WITH.maximum();

    /** The total, in the forms solved. */
    private static final int TOTAL = 0;

    /** The number of one element, in the forms that are of one element. */
    private static final int ELEMENT = 1;

    private CoupledCardinalityComposer() {}

    /**
     * A relation of a statement: {@code onElement} times the element's number plus
     * {@code onTotal} times the total plus {@code constant}, against nought.
     */
    private record Weighed(ExactRatio onElement, ExactRatio onTotal, ExactRatio constant, Rel rel) {}

    /** A relation standing in one of the ways it can: the form is in {@code region} of nought. */
    private record Outcome(Weighed relation, Rel region) {}

    /**
     * The counts and what they read.
     *
     * @param asked      the counts
     * @param number     the element's number
     * @param total      what the statements read of the container: the number summed
     * @param relations  the relations of each statement
     * @param carrier    the order the number is written on
     * @param kept       the place whose different values among the elements meeting a statement
     *                   are what is counted, or null where the elements are
     * @param keptCount  which of the counts that is, where there is such a place
     */
    record Coupled(List<CardinalityComposer.Asked.SoManyMeeting> asked,
                   NumericTerm.ValueOf number, NumericTerm total,
                   List<List<AStatementAtARow.AffineRelation>> relations, Carrier carrier,
                   TermPath kept, int keptCount) {

        /**
         * The counts as this composes them, or null where a statement reads anything besides forms
         * of a number of the element, the total of that number and numbers outside every
         * container, or where the different values of more than one place are counted.
         */
        static Coupled of(List<CardinalityComposer.Asked> asked, TermPath container,
                          Quantities measuring) {
            if (asked.isEmpty() || asked.size() > MOST_STATEMENTS) {
                return null;
            }
            List<CardinalityComposer.Asked.SoManyMeeting> counts = new ArrayList<>();
            TermPath kept = null;
            int keptCount = -1;
            for (CardinalityComposer.Asked each : asked) {
                if (!(each instanceof CardinalityComposer.Asked.SoManyMeeting many)
                        || many.across().isPresent()) {
                    return null;
                }
                if (many.differentAt().isPresent()) {
                    Quantity.TheValue at = many.differentAt().get();
                    if (!(at instanceof Quantity.TheValue.AtAPlace) || at.heldAt().size() != 1
                            || kept != null) {
                        return null;
                    }
                    kept = at.heldAt().getFirst();
                    keptCount = counts.size();
                }
                counts.add(many);
            }
            NumericTerm.ValueOf own = null;
            NumericTerm total = null;
            for (CardinalityComposer.Asked.SoManyMeeting many : counts) {
                for (NumericTerm term : many.perElement().numbers()) {
                    if (term instanceof NumericTerm.ValueOf value
                            && value.position().isAtOrUnder(container.element())
                            && !value.position().equals(container.element())
                            && (own == null || own.equals(value))) {
                        own = value;
                    } else if (term instanceof NumericTerm.TakenOver over
                            && SUM.equals(over.operation())
                            && over.source() instanceof RunSource.ProjectedOccurrences
                            && (total == null || total.equals(over))) {
                        total = over;
                    } else if (!term.subjectPath().insideAContainer()) {
                        // Beside the elements, at the one value the row was fixed at.
                        continue;
                    } else {
                        return null;
                    }
                }
            }
            if (own == null || total == null || !total.subjectPath().equals(own.position())
                    || (kept != null && (kept.equals(own.position())
                            || !kept.isAtOrUnder(container.element())))) {
                return null;
            }
            List<List<AStatementAtARow.AffineRelation>> relations = new ArrayList<>();
            int all = 0;
            for (CardinalityComposer.Asked.SoManyMeeting many : counts) {
                Optional<List<AStatementAtARow.AffineRelation>> forms =
                        many.perElement().affineRelations();
                if (forms.isEmpty()) {
                    return null;
                }
                all += forms.get().size();
                relations.add(forms.get());
            }
            if (all == 0 || all > MOST_RELATIONS) {
                return null;
            }
            TermOrders orders = measuring.ordersOf(own);
            Carrier carrier = orders == null ? null : orders.observed();
            if (carrier == null || !carrier.counts()
                    || carrier.onTheGrid(new Count(BigDecimal.valueOf(5, 1))) != null) {
                return null;
            }
            return new Coupled(List.copyOf(counts), own, total, List.copyOf(relations), carrier,
                    kept, keptCount);
        }
    }

    /**
     * The relations of each statement as weights of the element's number and the total, with the
     * numbers beside the elements put in the constant at the values the row was fixed at — or null
     * where one of them is not fixed at one.
     */
    private static List<List<Weighed>> weighed(Coupled coupled, Map<NumericTerm, Place> beside,
                                               Set<CompositionCapacity> unheld) {
        List<List<Weighed>> out = new ArrayList<>();
        for (List<AStatementAtARow.AffineRelation> statement : coupled.relations()) {
            List<Weighed> weighed = new ArrayList<>();
            for (AStatementAtARow.AffineRelation each : statement) {
                ExactRatio constant = each.form().constant();
                for (Map.Entry<NumericTerm, ExactRatio> weight : each.form().coefs().entrySet()) {
                    if (weight.getKey().equals(coupled.number())
                            || weight.getKey().equals(coupled.total())) {
                        continue;
                    }
                    Place at = beside.get(weight.getKey());
                    if (at == null) {
                        return null;
                    }
                    ExactRatio before = constant;
                    switch (weight.getValue().times(Count.number(at).exactly())
                            .flatMap(before::plus)) {
                        case ExactAnswer.Held<ExactRatio>(ExactRatio sum) -> constant = sum;
                        case ExactAnswer.Unheld<ExactRatio>(var why) -> {
                            unheld.add(new CompositionCapacity(
                                    CompositionCapacity.Where.VALUES_A_TOTAL_IS_SPREAD_OVER, why));
                            return null;
                        }
                    }
                }
                weighed.add(new Weighed(
                        each.form().coefs().getOrDefault(coupled.number(), ExactRatio.ZERO),
                        each.form().coefs().getOrDefault(coupled.total(), ExactRatio.ZERO),
                        constant, each.rel()));
            }
            out.add(List.copyOf(weighed));
        }
        return List.copyOf(out);
    }

    /**
     * Containers of {@code sourceType} for the counts {@code coupled} reads.
     *
     * @return the containers, or null where the counts are ones this does not compose
     */
    static TermRealizations.Realization compose(Coupled coupled, TermPath container,
                                                NumericSet size, Type sourceType,
                                                Shape.Sequence holding, Quantities measuring,
                                                SearchRegion within, RuleReadingContext reading) {
        NumericDomain.Bounds run = switch (within.projectionOf(coupled.number())) {
            case NumericDomain.FormProjection.Within(NumericDomain.Bounds held) ->
                    held == null ? NumericDomain.Bounds.OPEN : held;
            case NumericDomain.FormProjection.NothingIsLeft _ -> null;
            case null -> NumericDomain.Bounds.OPEN;
        };
        if (run == null) {
            return CardinalityComposer.none("no value of `" + coupled.number() + "` is left for the"
                    + " elements of `" + container + "`");
        }
        WholeNumbersLeft domain = WholeNumbersLeft.of(run);
        if (domain == null) {
            return null;
        }
        Map<TermPath, ObservedValue> written = new HashMap<>();
        Map<NumericTerm, Place> beside = CardinalityComposer.settledOutside(
                new ArrayList<CardinalityComposer.Asked>(coupled.asked()), measuring, within,
                written);
        Set<CompositionCapacity> unheld = new LinkedHashSet<>();
        List<List<Weighed>> relations = weighed(coupled, beside, unheld);
        if (relations == null) {
            return null;
        }
        return new Composition(coupled, relations, written, unheld, container, size, sourceType,
                holding, measuring, within, reading, domain).run();
    }

    /**
     * A row holding one element, read as if the container it is in came to a total, and the
     * element's number were a given one: what the statements read at the number is the given one,
     * and what they read over the container is the number and what is left of the total beside it.
     */
    private record WithTheTotal(BorderQuantity.Observation holding, TermPath place,
                                ObservedValue own, ObservedValue rest)
            implements BorderQuantity.Observation {

        @Override
        public WalkResult<ObservationAtPoint> at(TermPath path) {
            return path.equals(place) ? WalkResult.reached(new ObservationAtPoint.Value(own))
                    : holding.at(path);
        }

        @Override
        public WalkResult<List<ObservedValue>> everyValueAt(TermPath path) {
            return path.equals(place) ? WalkResult.reached(List.of(own, rest))
                    : holding.everyValueAt(path);
        }

        @Override
        public WalkResult<List<BorderQuantity.Observation>> eachElementOf(TermPath of) {
            return holding.eachElementOf(of);
        }
    }

    /**
     * What the elements of a container may be while one way of standing holds of each of the
     * relations, and what the statements answer there.
     *
     * @param cell   the ways the relations of every statement stand
     * @param meets  for each statement, in the order of the counts, whether it holds of the element
     * @param listed which of the listings of the element's other positions the answers were read at
     */
    private record Kind(List<Outcome> cell, boolean[] meets, int listed) {}

    /** The totals a bound leaves, over the rationals: either end may be missing. */
    private record Span(ExactRatio low, boolean lowStrict, ExactRatio high, boolean highStrict) {}

    private static final class Composition {

        private final Coupled coupled;
        private final List<List<Weighed>> relations;
        private final Map<TermPath, ObservedValue> written;
        private final NumericSet size;
        private final List<CardinalityComposer.Asked> counts;
        private final TermPath container;
        private final Type sourceType;
        private final Shape.Sequence holding;
        private final Quantities measuring;
        private final SearchRegion within;
        private final RuleReadingContext reading;
        private final WholeNumbersLeft domain;
        private final NumericTerm.ValueOf number;
        private final Carrier carrier;
        private final CardinalityComposer.Standing standing;

        private final Set<CompositionCapacity> unheld;
        private final Set<CompositionRepertoire> unnamed =
                EnumSet.noneOf(CompositionRepertoire.class);
        private final Set<CompositionBudget> refused = EnumSet.noneOf(CompositionBudget.class);

        /** The listings of an element's other positions, by the number and the offered value of
         *  the counted position the element is read with. */
        private final Map<String, ListedAt> listings = new HashMap<>();
        private List<ObservedValue> keptValues;
        private boolean keptValuesAsked;
        private ElementValues anyListing;

        private final List<FixtureTemplate> built = new ArrayList<>();
        private int shares;
        private boolean stoppedEarly;

        Composition(Coupled coupled, List<List<Weighed>> relations,
                    Map<TermPath, ObservedValue> written, Set<CompositionCapacity> unheld,
                    TermPath container, NumericSet size, Type sourceType, Shape.Sequence holding,
                    Quantities measuring, SearchRegion within, RuleReadingContext reading,
                    WholeNumbersLeft domain) {
            this.coupled = coupled;
            this.relations = relations;
            this.written = written;
            this.unheld = unheld;
            this.size = size;
            this.counts = new ArrayList<>(coupled.asked());
            this.container = container;
            this.sourceType = sourceType;
            this.holding = holding;
            this.measuring = measuring;
            this.within = within;
            this.reading = reading;
            this.domain = domain;
            this.number = coupled.number();
            this.carrier = coupled.carrier();
            this.standing = new CardinalityComposer.Standing.WhereItIsWritten(sourceType, reading);
        }

        /** What is listed of the element's other positions, and whether it is all of them. */
        private record ListedAt(List<ObservedValue> values, boolean all) {}

        TermRealizations.Realization run() {
            BigInteger placeholder = domain.one();
            if (placeholder == null) {
                return CardinalityComposer.none("no whole number is left for the elements of `"
                        + container + "`");
            }
            ListedAt first = listed(placeholder, 0);
            if (first == null || first.values().isEmpty()) {
                return CardinalityComposer.notChosen("an element of `" + container + "` has a part"
                        + " whose values are neither one of so many nor numbers the statements part");
            }
            if (!first.all()) {
                refused.add(CompositionBudget.VALUES_AN_ELEMENT_IS_CHOSEN_AMONG);
            }
            List<BorderQuantity.Observation> observed = new ArrayList<>();
            for (ObservedValue each : first.values()) {
                observed.add(observing(List.of(each)));
            }
            List<Kind> kinds = kinds(observed);
            if (!kinds.isEmpty()) {
                walk(kinds);
            }
            if (!stoppedEarly) {
                refused.add(CompositionBudget.ELEMENTS_A_COUNT_IS_COMPOSED_WITH);
            }
            CompositionShortfall shortfall = CompositionShortfall.of(refused, unnamed, unheld);
            if (!built.isEmpty()) {
                return new TermRealizations.Realization.Built(built, shortfall);
            }
            if (!shortfall.figures().isEmpty()) {
                return new TermRealizations.Realization.Stopped(shortfall);
            }
            return new TermRealizations.Realization.Unexhausted(shortfall, "what an element of `"
                    + container + "` answers turns on the total of `" + number + "`, and no"
                    + " container this composed meets the counts");
        }

        /** A row holding a container of these elements, with the numbers beside them written. */
        private BorderQuantity.Observation observing(List<ObservedValue> values) {
            return standing.read(CardinalityComposer.withNumbersBeside(
                    anyListing.holding(sourceType, values), written));
        }

        // ---- the element's other positions

        /**
         * The element listed with its number at {@code at} and, where the different values of a
         * place are counted, that place at the {@code offered}-th value offered for it — or null
         * where the element cannot be listed so.
         */
        private ListedAt listed(BigInteger at, int offered) {
            String key = at + "/" + offered;
            ListedAt known = listings.get(key);
            if (known != null) {
                return known;
            }
            Place place = carrier.onTheGrid(new Count(new BigDecimal(at)));
            if (place == null) {
                return null;
            }
            ElementValues listing = ElementValues.of(container, holding.element(), reading,
                    (position, part) -> {
                        if (position.equals(number.position())) {
                            return List.of(carrier.valueOf(place));
                        }
                        if (position.equals(coupled.kept())) {
                            if (!keptValuesAsked) {
                                keptValuesAsked = true;
                                keptValues = CardinalityComposer.numbersAt(position,
                                        CardinalityComposer.OfTheType.manyOf(part, reading),
                                        counts, null, measuring, within, Map.of(), MOST_ELEMENTS,
                                        unheld, unnamed, reading.today());
                            }
                            return keptValues == null || keptValues.size() <= offered ? null
                                    : List.of(keptValues.get(offered));
                        }
                        List<ObservedValue> values = CardinalityComposer.numbersAt(position,
                                CardinalityComposer.OfTheType.of(part, reading), counts, null,
                                measuring, within, Map.of(), 1, unheld, unnamed, reading.today());
                        return values == null || values.isEmpty() ? values
                                : List.of(values.getFirst());
                    });
            if (listing == null) {
                return null;
            }
            anyListing = listing;
            ListedAt out = new ListedAt(listing.listed().values(), listing.listed().all());
            listings.put(key, out);
            return out;
        }

        // ---- the ways the relations stand

        private ExactRatio held(ExactAnswer<ExactRatio> answer) {
            return switch (answer) {
                case ExactAnswer.Held<ExactRatio>(ExactRatio value) -> value;
                case ExactAnswer.Unheld<ExactRatio>(var why) -> {
                    unheld.add(new CompositionCapacity(
                            CompositionCapacity.Where.VALUES_A_TOTAL_IS_SPREAD_OVER, why));
                    yield null;
                }
            };
        }

        /** Every way the relations of the statements can stand, one for each. */
        private List<List<Outcome>> cells() {
            List<List<Outcome>> out = new ArrayList<>();
            out.add(List.of());
            for (List<Weighed> statement : relations) {
                for (Weighed relation : statement) {
                    List<Rel> regions = switch (relation.rel()) {
                        case EQ, NE -> List.of(Rel.LT, Rel.EQ, Rel.GT);
                        case GE, GT, LE, LT -> List.of(relation.rel(), relation.rel().denied());
                    };
                    List<List<Outcome>> next = new ArrayList<>();
                    for (List<Outcome> before : out) {
                        for (Rel region : regions) {
                            List<Outcome> cell = new ArrayList<>(before);
                            cell.add(new Outcome(relation, region));
                            next.add(List.copyOf(cell));
                        }
                    }
                    out = next;
                }
            }
            return out;
        }

        private static LinearForm<Integer> formOf(Map<Integer, ExactRatio> weights,
                                                  ExactRatio constant) {
            Map<Integer, ExactRatio> kept = new HashMap<>();
            weights.forEach((atom, weight) -> {
                if (!weight.isZero()) {
                    kept.put(atom, weight);
                }
            });
            return new LinearForm<>(constant, kept);
        }

        private static List<LaterNumbersEliminated.Bound<Integer>> boundsOf(
                LinearForm<Integer> form, Rel region) {
            return switch (region) {
                case LT -> List.of(new LaterNumbersEliminated.Bound<>(form, true));
                case LE -> List.of(new LaterNumbersEliminated.Bound<>(form, false));
                case GT -> List.of(new LaterNumbersEliminated.Bound<>(form.negate(), true));
                case GE -> List.of(new LaterNumbersEliminated.Bound<>(form.negate(), false));
                case EQ -> List.of(new LaterNumbersEliminated.Bound<>(form, false),
                        new LaterNumbersEliminated.Bound<>(form.negate(), false));
                case NE -> throw new IllegalStateException("a relation stands below or above"
                        + " nought and never apart from it");
            };
        }

        /** The numbers an element may be at the total {@code at}, in the cell. */
        private WholeNumbersLeft intervalAt(List<Outcome> cell, BigInteger at) {
            WholeNumbersLeft left = domain;
            for (Outcome outcome : cell) {
                Weighed relation = outcome.relation();
                ExactRatio total = held(relation.onTotal().times(ExactRatio.of(at)));
                ExactRatio constant = total == null ? null : held(total.plus(relation.constant()));
                if (constant == null) {
                    return null;
                }
                left = left.meeting(relation.onElement(), constant, outcome.region());
                if (left == null) {
                    return null;
                }
            }
            return left;
        }

        /** The totals the bounds leave, or null where they leave none. */
        private Span spanOf(List<LaterNumbersEliminated.Bound<Integer>> level) {
            ExactRatio low = null;
            boolean lowStrict = false;
            ExactRatio high = null;
            boolean highStrict = false;
            for (LaterNumbersEliminated.Bound<Integer> bound : level) {
                ExactRatio weight = bound.form().coefs().get(TOTAL);
                if (weight == null) {
                    int sign = bound.form().constant().signum();
                    if (bound.strict() ? sign >= 0 : sign > 0) {
                        return null;
                    }
                    continue;
                }
                ExactRatio at = held(bound.form().constant().negated().dividedBy(weight));
                if (at == null) {
                    return null;
                }
                if (weight.signum() > 0) {
                    int against = high == null ? -1 : at.compareTo(high);
                    if (against < 0 || (against == 0 && bound.strict())) {
                        high = at;
                        highStrict = bound.strict();
                    }
                } else {
                    int against = low == null ? 1 : at.compareTo(low);
                    if (against > 0 || (against == 0 && bound.strict())) {
                        low = at;
                        lowStrict = bound.strict();
                    }
                }
            }
            return new Span(low, lowStrict, high, highStrict);
        }

        /** The whole numbers a total is tried at in the span, the nearest nought first. */
        private List<BigInteger> totalsIn(Span span) {
            BigInteger low = null;
            BigInteger high = null;
            if (span.low() != null) {
                if (!(span.low().ceiling() instanceof ExactAnswer.Held<BigInteger>(var up))) {
                    return List.of();
                }
                low = span.lowStrict() && span.low().isWhole() ? up.add(BigInteger.ONE) : up;
            }
            if (span.high() != null) {
                if (!(span.high().floor() instanceof ExactAnswer.Held<BigInteger>(var down))) {
                    return List.of();
                }
                high = span.highStrict() && span.high().isWhole()
                        ? down.subtract(BigInteger.ONE) : down;
            }
            if (low != null && high != null && low.compareTo(high) > 0) {
                return List.of();
            }
            BigInteger nearest = BigInteger.ZERO;
            if (low != null && nearest.compareTo(low) < 0) {
                nearest = low;
            }
            if (high != null && nearest.compareTo(high) > 0) {
                nearest = high;
            }
            Set<BigInteger> out = new LinkedHashSet<>();
            BigInteger[] bases = {nearest, low, high};
            for (int away = 0; away <= MOST_TOTALS && out.size() < MOST_TOTALS; away++) {
                for (BigInteger base : bases) {
                    if (base == null) {
                        continue;
                    }
                    for (int sign = 1; sign >= -1; sign -= 2) {
                        BigInteger at = base.add(BigInteger.valueOf((long) sign * away));
                        if ((low == null || at.compareTo(low) >= 0)
                                && (high == null || at.compareTo(high) <= 0)
                                && out.size() < MOST_TOTALS) {
                            out.add(at);
                        }
                    }
                }
            }
            boolean every = low != null && high != null
                    && high.subtract(low).add(BigInteger.ONE).compareTo(
                            BigInteger.valueOf(MOST_TOTALS)) <= 0;
            if (!every) {
                refused.add(CompositionBudget.TOTALS_A_SHARING_IS_TRIED_AT);
            }
            return List.copyOf(out);
        }

        /**
         * The number and total at which {@code cell} stands, or null where there are none to be
         * found.
         */
        private BigInteger[] standingIn(List<Outcome> cell) {
            Map<Integer, ExactRatio> weights = new HashMap<>();
            List<LaterNumbersEliminated.Bound<Integer>> bounds = new ArrayList<>();
            for (Outcome outcome : cell) {
                Weighed relation = outcome.relation();
                weights.clear();
                weights.put(ELEMENT, relation.onElement());
                weights.put(TOTAL, relation.onTotal());
                bounds.addAll(boundsOf(formOf(weights, relation.constant()), outcome.region()));
            }
            addDomain(bounds, ELEMENT, ExactRatio.ONE);
            LaterNumbersEliminated<Integer> solved =
                    LaterNumbersEliminated.of(bounds, List.of(TOTAL, ELEMENT), MOST_PAIRS);
            if (solved instanceof LaterNumbersEliminated.StoppedShort<Integer>) {
                refused.add(CompositionBudget.PAIRS_OF_BOUNDS_A_TOTAL_IS_SOLVED_WITH);
                return null;
            }
            if (!(solved instanceof LaterNumbersEliminated.Eliminated<Integer> eliminated)) {
                return null;
            }
            Span span = spanOf(eliminated.levels().getFirst());
            if (span == null) {
                return null;
            }
            for (BigInteger total : totalsIn(span)) {
                WholeNumbersLeft left = intervalAt(cell, total);
                BigInteger at = left == null ? null : left.one();
                if (at != null) {
                    return new BigInteger[] {total, at};
                }
            }
            return null;
        }

        /** The bounds the numbers of the elements the weight stands for keep to. */
        private void addDomain(List<LaterNumbersEliminated.Bound<Integer>> bounds, int atom,
                               ExactRatio weight) {
            if (domain.least() != null) {
                ExactRatio least = held(weight.times(ExactRatio.of(domain.least())));
                if (least != null) {
                    bounds.add(new LaterNumbersEliminated.Bound<>(
                            formOf(Map.of(atom, ExactRatio.ONE.negated()), least), false));
                }
            }
            if (domain.most() != null) {
                ExactRatio most = held(weight.times(ExactRatio.of(domain.most())));
                if (most != null) {
                    bounds.add(new LaterNumbersEliminated.Bound<>(
                            formOf(Map.of(atom, ExactRatio.ONE), most.negated()), false));
                }
            }
        }

        /**
         * What each statement answers of an element in a container coming to {@code total}, or
         * null where one could not be read.
         */
        private boolean[] answers(BorderQuantity.Observation element, BigInteger total,
                                  BigInteger at) {
            Place own = carrier.onTheGrid(new Count(new BigDecimal(at)));
            Place left = carrier.onTheGrid(new Count(new BigDecimal(total.subtract(at))));
            if (own == null || left == null) {
                return null;
            }
            BorderQuantity.Observation read = new WithTheTotal(element, number.position(),
                    carrier.valueOf(own), carrier.valueOf(left));
            boolean[] out = new boolean[coupled.asked().size()];
            for (int count = 0; count < out.length; count++) {
                switch (coupled.asked().get(count).perElement().at(read)) {
                    case AStatementAtARow.Answer.Holds _ -> out[count] = true;
                    case AStatementAtARow.Answer.Fails _ -> out[count] = false;
                    case AStatementAtARow.Answer.CouldNotTell _ -> {
                        return null;
                    }
                }
            }
            return out;
        }

        /** Each way the relations can stand, with what the statements answer there. */
        private List<Kind> kinds(List<BorderQuantity.Observation> observed) {
            List<Kind> out = new ArrayList<>();
            for (List<Outcome> cell : cells()) {
                BigInteger[] probe = standingIn(cell);
                if (probe == null) {
                    continue;
                }
                Set<List<Boolean>> seen = new LinkedHashSet<>();
                for (int listed = 0; listed < observed.size(); listed++) {
                    boolean[] meets = answers(observed.get(listed), probe[0], probe[1]);
                    if (meets == null) {
                        unnamed.add(CompositionRepertoire.ELEMENTS_CHOSEN_FOR_A_COUNT);
                        continue;
                    }
                    List<Boolean> key = new ArrayList<>();
                    for (boolean each : meets) {
                        key.add(each);
                    }
                    if (seen.add(key)) {
                        out.add(new Kind(cell, meets, listed));
                    }
                }
            }
            return out;
        }

        // ---- the sharings

        private void walk(List<Kind> kinds) {
            for (int held = 0; held <= MOST_ELEMENTS && !stoppedEarly; held++) {
                if (size != null && !size.holds(Count.of(held), Carrier.WHOLE)) {
                    continue;
                }
                if (!sharings(kinds, 0, held, new int[kinds.size()],
                        shared -> tried(kinds, shared))) {
                    stoppedEarly = true;
                }
            }
        }

        private static boolean sharings(List<?> kinds, int kind, int left, int[] counts,
                                        Predicate<int[]> each) {
            if (kind == kinds.size() - 1) {
                counts[kind] = left;
                return each.test(counts);
            }
            for (int count = 0; count <= left; count++) {
                counts[kind] = count;
                if (!sharings(kinds, kind + 1, left - count, counts, each)) {
                    return false;
                }
            }
            return true;
        }

        /** How many elements of this sharing meet each statement. */
        private int[] meeting(List<Kind> kinds, int[] counts) {
            int[] out = new int[coupled.asked().size()];
            for (int kind = 0; kind < kinds.size(); kind++) {
                for (int count = 0; count < out.length; count++) {
                    out[count] += kinds.get(kind).meets()[count] ? counts[kind] : 0;
                }
            }
            return out;
        }

        /**
         * How many each count is of, for those meeting the statement: the elements, or the
         * different values of the place they hold, which are one to as many as they are.
         * Every way of counting that meets all the counts asked.
         */
        private List<int[]> counted(int[] meeting) {
            List<int[]> out = new ArrayList<>();
            int[] chosen = new int[meeting.length];
            int kept = coupled.keptCount();
            for (int count = 0; count < meeting.length; count++) {
                if (count != kept && !coupled.asked().get(count).asMany(meeting[count])) {
                    return out;
                }
                chosen[count] = meeting[count];
            }
            if (kept < 0) {
                out.add(chosen);
                return out;
            }
            for (int different = meeting[kept] > 0 ? 1 : 0; different <= meeting[kept];
                    different++) {
                if (coupled.asked().get(kept).asMany(different)) {
                    int[] one = chosen.clone();
                    one[kept] = different;
                    out.add(one);
                }
            }
            return out;
        }

        /** Looks for a container of this sharing; false to stop the walk. */
        private boolean tried(List<Kind> kinds, int[] sharing) {
            List<int[]> counted = counted(meeting(kinds, sharing));
            if (counted.isEmpty()) {
                return true;
            }
            if (shares++ == MOST_SHARES) {
                refused.add(CompositionBudget.SHARES_A_COUNT_IS_TRIED_AT);
                return false;
            }
            List<Integer> active = new ArrayList<>();
            int held = 0;
            for (int kind = 0; kind < sharing.length; kind++) {
                if (sharing[kind] > 0) {
                    active.add(kind);
                    held += sharing[kind];
                }
            }
            List<BigInteger> totals = held == 0 ? List.of(BigInteger.ZERO)
                    : totalsOf(kinds, sharing, active);
            for (BigInteger total : totals) {
                for (int[] count : counted) {
                    List<ObservedValue> values = valuesOf(kinds, sharing, active, total, count);
                    if (values == null) {
                        continue;
                    }
                    BorderQuantity.Observation whole = observing(values);
                    boolean every = true;
                    for (CardinalityComposer.Asked each : counts) {
                        every &= each.over(container, List.of(), whole)
                                instanceof AStatementAtARow.Answer.Holds;
                    }
                    if (!every) {
                        continue;
                    }
                    TermRealizations.Realization rows =
                            standing.written(values, MOST_OFFERED - built.size());
                    if (rows instanceof TermRealizations.Realization.Built offered) {
                        offered.values().forEach(built::add);
                    }
                    if (rows != null) {
                        CompositionShortfall met = rows.shortfall();
                        refused.addAll(met.figures());
                        unnamed.addAll(met.populations());
                        unheld.addAll(met.unheld());
                    }
                    if (built.size() >= MOST_OFFERED) {
                        refused.add(CompositionBudget.CONTAINERS_A_COUNT_IS_OFFERED);
                        return false;
                    }
                    return true;
                }
            }
            return true;
        }

        /** The whole numbers a container of this sharing can come to, tried in turn. */
        private List<BigInteger> totalsOf(List<Kind> kinds, int[] sharing, List<Integer> active) {
            List<LaterNumbersEliminated.Bound<Integer>> bounds = new ArrayList<>();
            // The total is what the elements of every kind come to.
            Map<Integer, ExactRatio> comes = new HashMap<>();
            comes.put(TOTAL, ExactRatio.ONE.negated());
            for (int at = 0; at < active.size(); at++) {
                comes.put(at + 1, ExactRatio.ONE);
            }
            LinearForm<Integer> equal = formOf(comes, ExactRatio.ZERO);
            bounds.add(new LaterNumbersEliminated.Bound<>(equal, false));
            bounds.add(new LaterNumbersEliminated.Bound<>(equal.negate(), false));
            for (int at = 0; at < active.size(); at++) {
                ExactRatio count = ExactRatio.of(sharing[active.get(at)]);
                for (Outcome outcome : kinds.get(active.get(at)).cell()) {
                    Weighed relation = outcome.relation();
                    ExactRatio onTotal = held(count.times(relation.onTotal()));
                    ExactRatio constant = held(count.times(relation.constant()));
                    if (onTotal == null || constant == null) {
                        return List.of();
                    }
                    Map<Integer, ExactRatio> weights = new HashMap<>();
                    weights.put(at + 1, relation.onElement());
                    weights.put(TOTAL, onTotal);
                    bounds.addAll(boundsOf(formOf(weights, constant), outcome.region()));
                }
                addDomain(bounds, at + 1, count);
            }
            List<Integer> order = new ArrayList<>();
            for (int atom = 0; atom <= active.size(); atom++) {
                order.add(atom);
            }
            LaterNumbersEliminated<Integer> solved =
                    LaterNumbersEliminated.of(bounds, order, MOST_PAIRS);
            if (solved instanceof LaterNumbersEliminated.StoppedShort<Integer>) {
                refused.add(CompositionBudget.PAIRS_OF_BOUNDS_A_TOTAL_IS_SOLVED_WITH);
                return List.of();
            }
            if (!(solved instanceof LaterNumbersEliminated.Eliminated<Integer> eliminated)) {
                return List.of();
            }
            Span span = spanOf(eliminated.levels().getFirst());
            return span == null ? List.of() : totalsIn(span);
        }

        /**
         * The elements of the container of this sharing coming to {@code total}, each to a value
         * of its own where the interval its kind leaves it allows, and the places of the counted
         * position offered to those meeting the statement it is counted for — or null where there
         * is none.
         *
         * @param counted for each statement, how many it is counted to
         */
        private List<ObservedValue> valuesOf(List<Kind> kinds, int[] sharing, List<Integer> active,
                                             BigInteger total, int[] counted) {
            List<Kind> chosen = new ArrayList<>();
            List<BigInteger[]> bounds = new ArrayList<>();
            BigInteger lowest = BigInteger.ZERO;
            BigInteger highest = BigInteger.ZERO;
            boolean lowestKnown = true;
            boolean highestKnown = true;
            for (int kind : active) {
                WholeNumbersLeft left = intervalAt(kinds.get(kind).cell(), total);
                if (left == null || left.one() == null) {
                    return null;
                }
                BigInteger count = BigInteger.valueOf(sharing[kind]);
                lowestKnown &= left.least() != null;
                highestKnown &= left.most() != null;
                lowest = left.least() == null ? lowest : lowest.add(left.least().multiply(count));
                highest = left.most() == null ? highest : highest.add(left.most().multiply(count));
                for (int each = 0; each < sharing[kind]; each++) {
                    chosen.add(kinds.get(kind));
                    bounds.add(new BigInteger[] {left.least(), left.most()});
                }
            }
            if ((lowestKnown && total.compareTo(lowest) < 0)
                    || (highestKnown && total.compareTo(highest) > 0)) {
                return null;
            }
            BigInteger[] at = new BigInteger[chosen.size()];
            BigInteger sum = BigInteger.ZERO;
            for (int each = 0; each < at.length; each++) {
                BigInteger least = bounds.get(each)[0];
                BigInteger most = bounds.get(each)[1];
                BigInteger start = BigInteger.ZERO;
                if (least != null && start.compareTo(least) < 0) {
                    start = least;
                }
                if (most != null && start.compareTo(most) > 0) {
                    start = most;
                }
                at[each] = start;
                sum = sum.add(start);
            }
            BigInteger delta = total.subtract(sum);
            for (int each = 0; each < at.length && delta.signum() != 0; each++) {
                BigInteger edge = bounds.get(each)[delta.signum() > 0 ? 1 : 0];
                BigInteger reach = edge == null ? delta : edge.subtract(at[each]);
                BigInteger step = delta.signum() > 0 ? delta.min(reach) : delta.max(reach);
                at[each] = at[each].add(step);
                delta = delta.subtract(step);
            }
            if (delta.signum() != 0) {
                return null;
            }
            List<ObservedValue> values = new ArrayList<>();
            int meetingSeen = 0;
            for (int each = 0; each < at.length; each++) {
                Kind kind = chosen.get(each);
                int offered = 0;
                if (coupled.kept() != null && kind.meets()[coupled.keptCount()]) {
                    offered = meetingSeen++ % counted[coupled.keptCount()];
                }
                ListedAt listed = listed(at[each], offered);
                if (listed == null || listed.values().size() <= kind.listed()) {
                    unnamed.add(CompositionRepertoire.ELEMENTS_CHOSEN_FOR_A_COUNT);
                    return null;
                }
                values.add(listed.values().get(kind.listed()));
            }
            return values;
        }
    }
}
