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
 * are an interval over the rationals ({@link TotalsASharingCanComeTo}); at each whole number in it
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
 * every container against nought ({@link AStatementAtARow#affineRelations}), nor for a number
 * that is not a whole number: those are left to the composition that does not read the total
 * ({@link CardinalityComposer}).
 */
final class CoupledCardinalityComposer {

    private static final ValueName.Stdlib.Operation SUM = ValueName.Stdlib.operation("List", "sum");

    /** The most statements counted together. Past it the counts are composed one at a time, as
     *  they are where nothing reads the total. */
    private static final int MOST_STATEMENTS = 3;

    /** The most relations, of all the statements, whose ways of standing are taken together. Each
     *  stands in two or three ways and the ways are all looked at before any sharing is, so this
     *  is what keeps them to a few dozen; the sharings after them are held to a figure of their
     *  own. */
    private static final int MOST_RELATIONS = 4;

    private static final int MOST_ELEMENTS =
            CompositionBudget.ELEMENTS_A_COUNT_IS_COMPOSED_WITH.maximum();

    private static final int MOST_OFFERED = CompositionBudget.CONTAINERS_A_COUNT_IS_OFFERED.maximum();

    private static final int MOST_SHARES = CompositionBudget.SHARES_A_COUNT_IS_TRIED_AT.maximum();

    private static final int MOST_TOTALS = CompositionBudget.TOTALS_A_COUNT_IS_TRIED_AT.maximum();

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
                    } else if (term.subjectPath().insideAContainer()) {
                        return null;
                    }
                }
            }
            if (own == null || total == null || !total.subjectPath().equals(own.position())
                    || (kept != null && (kept.equals(own.position())
                            || !kept.isAtOrUnder(container.element())))) {
                return null;
            }
            for (CardinalityComposer.Asked.SoManyMeeting many : counts) {
                for (TermPath read : many.perElement().positionsAsked()) {
                    if (!canBeReadAt(read, container, own.position(), kept)) {
                        return null;
                    }
                }
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
            if (!(carrier instanceof Carrier.Whole)) {
                return null;
            }
            return new Coupled(List.copyOf(counts), own, total, List.copyOf(relations), carrier,
                    kept, keptCount);
        }
    }

    /**
     * Whether a statement can ask of its own value the position {@code read}. The elements are
     * read in a row that holds the container, listed at every position but two, and the numbers
     * fixed beside it: a position inside an element is read off the listing, unless it is the
     * number, which is chosen here, or the place counted, which is offered values apart from what
     * the statements read. Nothing else is held for it to be read from.
     */
    private static boolean canBeReadAt(TermPath read, TermPath container, TermPath number,
                                       TermPath kept) {
        return read.isAtOrUnder(container.element()) && !overlap(read, number)
                && (kept == null || !overlap(read, kept));
    }

    private static boolean overlap(TermPath one, TermPath other) {
        return one.isAtOrUnder(other) || other.isAtOrUnder(one);
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
        // Where the region leaves the number nothing, no element can be, which is no end of what
        // can be composed: the container of none is still one.
        WholeNumbersLeft domain = switch (within.projectionOf(coupled.number())) {
            case NumericDomain.FormProjection.Within(NumericDomain.Bounds held) ->
                    WholeNumbersLeft.of(held == null ? NumericDomain.Bounds.OPEN : held);
            case NumericDomain.FormProjection.NothingIsLeft _ -> WholeNumbersLeft.NONE;
            case null -> WholeNumbersLeft.EVERY;
        };
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
    private record Kind(List<Outcome> cell, boolean[] meets, int listed,
                        TotalsASharingCanComeTo.Reach reach) {}

    private static final class Composition {

        private final Coupled coupled;
        private final List<List<Weighed>> relations;
        private final Map<TermPath, ObservedValue> written;
        private final NumericSet size;
        private final List<CardinalityComposer.Asked> counts;
        /** For each count, whether it asks for so many, from none to the most elements held. */
        private final boolean[][] asked;
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

        private final List<FixtureTemplate> built = new ArrayList<>();
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
            // Whether each count asks for so many is the same for every sharing, and asked of
            // every one it would be worked out again for each.
            this.asked = new boolean[counts.size()][MOST_ELEMENTS + 1];
            for (int count = 0; count < asked.length; count++) {
                for (int many = 0; many <= MOST_ELEMENTS; many++) {
                    asked[count][many] = counts.get(count).asMany(many);
                }
            }
        }

        /** What is listed of the element's other positions, and whether it is all of them. */
        private record ListedAt(List<ObservedValue> values, boolean all) {}

        TermRealizations.Realization run() {
            // The container of none needs no element, so it is looked at before anything of one.
            boolean room = size == null || size.holds(Count.of(0), Carrier.WHOLE);
            boolean none = room && meetsEveryCount(List.of());
            if (none && offer(List.of())) {
                stoppedEarly = true;
            }
            boolean elements = !stoppedEarly && walkTheElements();
            if (elements && !stoppedEarly) {
                refused.add(CompositionBudget.ELEMENTS_A_COUNT_IS_COMPOSED_WITH);
            }
            CompositionShortfall shortfall = CompositionShortfall.of(refused, unnamed, unheld);
            if (!built.isEmpty()) {
                return new TermRealizations.Realization.Built(built, shortfall);
            }
            if (!shortfall.figures().isEmpty()) {
                return new TermRealizations.Realization.Stopped(shortfall);
            }
            if (!shortfall.nothing()) {
                return new TermRealizations.Realization.Unexhausted(shortfall, "what an element of `"
                        + container + "` answers turns on the total of `" + number + "`, and no"
                        + " container this composed meets the counts");
            }
            return CardinalityComposer.none("no container of `" + container + "` meets the counts:"
                    + " no whole number is left for its elements, and the container of none does"
                    + " not meet them");
        }

        /**
         * Looks for containers of one element or more. False where there is no element to choose
         * the values of, and nothing was left unsaid about why.
         */
        private boolean walkTheElements() {
            BigInteger placeholder = domain.one();
            if (placeholder == null) {
                return false;
            }
            ListedAt first = listed(placeholder, 0);
            if (first == null || first.values().isEmpty()) {
                unnamed.add(CompositionRepertoire.ELEMENTS_CHOSEN_FOR_A_COUNT);
                return false;
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
            return true;
        }

        /** Whether a container of these elements meets every count, read whole. */
        private boolean meetsEveryCount(List<ObservedValue> values) {
            BorderQuantity.Observation whole = observing(values);
            for (CardinalityComposer.Asked each : counts) {
                if (!(each.over(container, List.of(), whole)
                        instanceof AStatementAtARow.Answer.Holds)) {
                    return false;
                }
            }
            return true;
        }

        /**
         * Writes rows holding a container of these elements, and keeps what they said of what was
         * not reached. True once as many have been offered as are to be.
         */
        private boolean offer(List<ObservedValue> values) {
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
                return true;
            }
            return false;
        }

        /** A row holding a container of these elements, with the numbers beside them written. */
        private BorderQuantity.Observation observing(List<ObservedValue> values) {
            return standing.read(CardinalityComposer.withNumbersBeside(
                    ElementValues.holding(container, reading, sourceType, values), written));
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

        /**
         * What a cell leaves an element: each relation of it is a bound on the element's number
         * that is a line in the total, or a bound on the total alone — or null where the exact
         * arithmetic could not hold it.
         */
        private TotalsASharingCanComeTo.Reach reachOf(List<Outcome> cell) {
            List<TotalsASharingCanComeTo.Line> lower = new ArrayList<>();
            List<TotalsASharingCanComeTo.Line> upper = new ArrayList<>();
            ExactRatio totalLow = null;
            ExactRatio totalHigh = null;
            for (Outcome outcome : cell) {
                Weighed relation = outcome.relation();
                // a · number + b · total + c in the region of nought: the number is in the
                // region, turned about where a weighs it below nought, of -(b · total + c) / a.
                ExactRatio weight = relation.onElement().isZero() ? relation.onTotal()
                        : relation.onElement();
                if (weight.isZero()) {
                    // Neither the number nor the total is in it: the relation stands this way
                    // everywhere or nowhere, and a way it never stands is no cell.
                    if (!outcome.region().holds(relation.constant().signum())) {
                        return null;
                    }
                    continue;
                }
                Rel region = weight.signum() < 0 ? outcome.region().turned() : outcome.region();
                if (relation.onElement().isZero()) {
                    ExactRatio at = held(relation.constant().negated().dividedBy(weight));
                    if (at == null) {
                        return null;
                    }
                    if (region == Rel.LT || region == Rel.LE || region == Rel.EQ) {
                        totalHigh = totalHigh == null || at.compareTo(totalHigh) < 0 ? at
                                : totalHigh;
                    }
                    if (region == Rel.GT || region == Rel.GE || region == Rel.EQ) {
                        totalLow = totalLow == null || at.compareTo(totalLow) > 0 ? at : totalLow;
                    }
                    continue;
                }
                ExactRatio slope = held(relation.onTotal().negated().dividedBy(weight));
                ExactRatio intercept = held(relation.constant().negated().dividedBy(weight));
                if (slope == null || intercept == null) {
                    return null;
                }
                TotalsASharingCanComeTo.Line line = new TotalsASharingCanComeTo.Line(slope,
                        intercept);
                if (region == Rel.LT || region == Rel.LE || region == Rel.EQ) {
                    upper.add(line);
                }
                if (region == Rel.GT || region == Rel.GE || region == Rel.EQ) {
                    lower.add(line);
                }
            }
            if (domain.least() != null) {
                lower.add(new TotalsASharingCanComeTo.Line(ExactRatio.ZERO,
                        ExactRatio.of(domain.least())));
            }
            if (domain.most() != null) {
                upper.add(new TotalsASharingCanComeTo.Line(ExactRatio.ZERO,
                        ExactRatio.of(domain.most())));
            }
            return new TotalsASharingCanComeTo.Reach(lower, upper, totalLow, totalHigh);
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

        /** The whole numbers a total is tried at in the interval, the nearest nought first. */
        private List<BigInteger> totalsIn(TotalsASharingCanComeTo.Interval span) {
            TotalsASharingCanComeTo.WholeNumbers found =
                    TotalsASharingCanComeTo.wholeNumbersIn(span, MOST_TOTALS);
            if (!found.all()) {
                refused.add(CompositionBudget.TOTALS_A_COUNT_IS_TRIED_AT);
            }
            return found.tried();
        }

        /**
         * The number and total at which {@code cell} stands, or null where there are none to be
         * found.
         */
        private BigInteger[] standingIn(List<Outcome> cell,
                                        TotalsASharingCanComeTo.Reach reach) {
            TotalsASharingCanComeTo.Interval totals =
                    TotalsASharingCanComeTo.whereAnElementCanBe(reach, unheld);
            if (totals == null) {
                return null;
            }
            for (BigInteger total : totalsIn(totals)) {
                WholeNumbersLeft left = intervalAt(cell, total);
                BigInteger at = left == null ? null : left.one();
                if (at != null) {
                    return new BigInteger[] {total, at};
                }
            }
            return null;
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
                TotalsASharingCanComeTo.Reach reach = reachOf(cell);
                BigInteger[] probe = reach == null ? null : standingIn(cell, reach);
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
                        out.add(new Kind(cell, meets, listed, reach));
                    }
                }
            }
            return out;
        }

        // ---- the sharings

        private void walk(List<Kind> kinds) {
            boolean[][] meets = new boolean[kinds.size()][];
            for (int kind = 0; kind < meets.length; kind++) {
                meets[kind] = kinds.get(kind).meets();
            }
            // Every sharing looked at, whole or part, is counted against the figure, and one that
            // cannot give a count asked for is dropped before the kinds after it are given any.
            SharingsAmongKinds sharings =
                    new SharingsAmongKinds(meets, asked, coupled.keptCount(), MOST_SHARES);
            // The container of none is looked at before this, apart from any element.
            for (int held = 1; held <= MOST_ELEMENTS && !stoppedEarly; held++) {
                if (size != null && !size.holds(Count.of(held), Carrier.WHOLE)) {
                    continue;
                }
                if (!sharings.ofSize(held, shared -> tried(kinds, shared))) {
                    stoppedEarly = true;
                }
            }
            if (sharings.spent()) {
                refused.add(CompositionBudget.SHARES_A_COUNT_IS_TRIED_AT);
            }
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
                if (count != kept && !asked[count][meeting[count]]) {
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
                if (asked[kept][different]) {
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
            List<Integer> active = new ArrayList<>();
            for (int kind = 0; kind < sharing.length; kind++) {
                if (sharing[kind] > 0) {
                    active.add(kind);
                }
            }
            for (BigInteger total : totalsOf(kinds, sharing, active)) {
                for (int[] count : counted) {
                    List<ObservedValue> values = valuesOf(kinds, sharing, active, total, count);
                    if (values != null && meetsEveryCount(values)) {
                        return !offer(values);
                    }
                }
            }
            return true;
        }

        /** The whole numbers a container of this sharing can come to, tried in turn. */
        private List<BigInteger> totalsOf(List<Kind> kinds, int[] sharing, List<Integer> active) {
            List<TotalsASharingCanComeTo.Reach> reaches = new ArrayList<>();
            int[] counts = new int[active.size()];
            for (int at = 0; at < counts.length; at++) {
                reaches.add(kinds.get(active.get(at)).reach());
                counts[at] = sharing[active.get(at)];
            }
            TotalsASharingCanComeTo.Interval found =
                    TotalsASharingCanComeTo.of(reaches, counts, unheld);
            return found == null ? List.of() : totalsIn(found);
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
