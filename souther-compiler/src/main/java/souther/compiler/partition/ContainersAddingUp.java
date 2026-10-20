package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.check.DeclaredBounds;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.Shape;
import souther.compiler.check.NumericMeasures;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.TypeView;
import souther.compiler.inputs.BoundaryDomain;
import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.ElementProjection;
import souther.compiler.inputs.ElementValue;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermPath;
import souther.compiler.inputs.TraversalDirection;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.CountDomain;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.UnheldNumber;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.math.RoundingMode;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.Deque;
import java.util.EnumSet;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

/**
 * Containers filled so that the occurrences of a path inside them come to a number.
 *
 * <p><b>One question, and the two ways a total is written are cases of it.</b> A total of a list at
 * a position adds up what the list holds, and a total over a run adds up what stands at a path
 * inside each element — the container is the same thing either way, and what differs is how far
 * down the number is. Written as two, the second would be the first's algorithm with an extra step,
 * free to disagree with it about how many elements a total is worth.
 *
 * <p><b>The elements are chosen against what the rules leave them.</b> How many the container may
 * hold is what its own type declares and what the record holding it says, tightened together; what
 * one occurrence may be is what the region leaves the number at that path. A container built without
 * asking either is one the decoder refuses, and the point it was built for then reads as an edge
 * every value was refused at rather than as one this did not fill.
 *
 * <p><b>And a range is not an existence proof.</b> That {@code k} elements between {@code lo} and
 * {@code hi} could reach the total is arithmetic on the ends, and the values between them are the
 * carrier's rather than every number in the interval. So a count the ends admit is a count to try,
 * and one whose decomposition does not land on the carrier is stepped over — the next count up is
 * asked the same question. Read as a proof, the first hole in an order would be a total nothing
 * composes a row for.
 *
 * <p>Nothing here decides whether the model admits what was built. Every element is a whole value
 * composed under its own type's rules, and the row it goes into is put through the module's own
 * decoder like any other — which is what makes the offer a row rather than a shape carrying a
 * number.
 */
final class ContainersAddingUp {

    /**
     * Containers whose occurrences of {@code target}'s path come to {@code answer}, or why there are
     * none.
     *
     * @param container what the target's root is declared to hold, which is what is written there
     * @param orders    the ends the term stands on. The elements are written on the order the answer
     *                  is measured on, which is the order the reading adds them up on — taken apart,
     *                  a container built here would be read as a different total than it was built
     *                  for
     */
    static TermRealizations.Realization to(Place answer, Type container,
                                           TermOrders orders, SearchRegion within,
                                           RuleReadingContext reading) {
        return to(answer, container, List.of(), orders, within, reading, null,
                DemandsInside.NOTHING);
    }

    /**
     * The same, with every element asked to hold {@code inside} beside the number.
     *
     * <p>Asked of the element's plan and of nothing after it. What an element holds at a position
     * the caller fixed, and which case a position the caller narrowed is, are things the plan is
     * made against — so an element that cannot hold them is a way down that does not plan, said
     * the way every other one is, and never an element built first and turned away for what it
     * holds.
     */
    static TermRealizations.Realization to(Place answer, Type container,
                                           List<List<String>> keptApart,
                                           TermOrders orders, SearchRegion within,
                                           RuleReadingContext reading, DemandsInside inside) {
        return to(answer, container, keptApart, orders, within, reading, null, inside);
    }

    /**
     * The same, where how many the container holds is asked for as well as what it comes to.
     *
     * <p><b>One more thing that says how many, and the counts are where they meet.</b> What the
     * declarations leave the container, what the rules leave it on the way, and what a group of
     * numbers at one location asks of it are three answers to one question, and a container is
     * written where all three admit its size. Read anywhere but the counts — as a filter on what
     * was built, say — a count the group refuses would be walked, filled and thrown away, and the
     * figure the walk holds to would be spent on sizes nobody asked for.
     *
     * @param keptApart   what the rules of the value holding the container keep its elements apart
     *                    at ({@link ElementsKeptApart}), beside what its own names do
     * @param alsoHolding how many it is asked to hold beside the total, or null where nothing but
     *                    the total is asked for
     * @param inside      what every element is asked to hold beside the number
     */
    static TermRealizations.Realization to(Place answer, Type container,
                                           List<List<String>> keptApart,
                                           TermOrders orders, SearchRegion within,
                                           RuleReadingContext reading,
                                           HowManyIsAskedFor alsoHolding,
                                           DemandsInside inside) {
        // What the caller asked inside an element contradicting itself is no way down that did not
        // plan: it is every way down, settled before any of them is tried. Met inside the walk it
        // was a refusal of one way that the walk had no account of.
        Optional<Requirements.Merge.Conflict> contradicts = inside.contradiction();
        if (contradicts.isPresent()) {
            Requirements.Merge.Conflict conflict = contradicts.get();
            return new TermRealizations.Realization.None(
                    Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE,
                    "what each element is asked to hold puts `" + conflict.at() + "` both at "
                            + conflict.one().spelled() + " and at " + conflict.other().spelled());
        }
        // The lists of a list put end to end: a container inside the elements of another, so an
        // element holds as many occurrences of the number as its own container does and the total is
        // spread over the leaves and then grouped, level by level.
        if (orders.term() instanceof NumericTerm.TakenOver over
                && over.source() instanceof RunSource.FlattenedOccurrences flat) {
            return new NestedContainersAddingUp(flat.subjectPath()).to(answer, container,
                    keptApart, orders, within, reading, alsoHolding, inside);
        }
        // A run computed of each element is written by solving for the one field its computation
        // reads, so the elements are chosen on that field's order and stand at its place. A
        // computation this does not solve for is a population this compiler writes none of, which
        // is not the same as the model admitting no row.
        if (orders.term() instanceof NumericTerm.TakenOver over
                && over.source() instanceof RunSource.ComputedOccurrences computed) {
            List<FieldSolved> ways = FieldSolved.of(computed, orders);
            if (ways.isEmpty()) {
                return new TermRealizations.Realization.Unexhausted(
                        CompositionShortfall.writing(
                                Set.of(CompositionRepertoire.ELEMENTS_A_COMPUTED_TOTAL_IS_SOLVED_FOR)),
                        null);
            }
            return throughEach(ways, solved -> composedThrough(solved, answer, container,
                    keptApart, orders, within, reading, alsoHolding, inside));
        }
        return composedThrough(null, answer, container, keptApart, orders, within, reading,
                alsoHolding, inside);
    }

    /**
     * What is written for one point by each way of solving for it, tried until one writes
     * something: the values of the first that does, and otherwise what every one of them came to
     * without.
     *
     * <p>Every way and not the first. A choice by case is solved for through each arm that is a
     * form of one field of its case, each writing the containers of that case alone, and which of
     * them reaches a point is the point's to say — a total only a fee reaches is reached by the
     * arm that adds the fee, whichever arm was written first.
     */
    private static TermRealizations.Realization throughEach(
            List<FieldSolved> ways,
            Function<FieldSolved, TermRealizations.Realization> composing) {
        TermRealizations.Realization last = null;
        CompositionShortfall met = CompositionShortfall.NONE;
        for (FieldSolved way : ways) {
            last = composing.apply(way);
            if (last instanceof TermRealizations.Realization.Built) {
                return last;
            }
            met = met.and(last.shortfall());
        }
        if (!met.figures().isEmpty()) {
            return new TermRealizations.Realization.Stopped(met);
        }
        return met.nothing() ? last : new TermRealizations.Realization.Unexhausted(met, null);
    }

    /**
     * What is written for {@code answer} where the elements are chosen on what {@code solved}
     * solves for, or on the total's own values where it is null.
     */
    private static TermRealizations.Realization composedThrough(
            FieldSolved solved, Place answer, Type container, List<List<String>> keptApart,
            TermOrders orders, SearchRegion within, RuleReadingContext reading,
            HowManyIsAskedFor alsoHolding, DemandsInside inside) {
        RuleReadingSource ruleSource = reading.source();
        // Which number is being built for, read off the answer that says which number it is of.
        // Named beside it, the two were free to be about two numbers and this would fill a
        // container found under one path with elements counted on another's order.
        RealizationTarget.OfANumber target = RealizationTarget.of(orders.term());
        Carrier elements = solved == null ? orders.answered() : solved.carrier();
        TermPath occurring = solved == null ? occurrences(target) : solved.field();
        if (!(answer instanceof Count total) || elements == null) {
            return none(Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
        }
        // The position, read once. What it holds, how many of them its rules leave it holding, and
        // the names the container is written under are three questions of one reading, and asking
        // the type again for any of them is another answer to which names it wears.
        TypeView view = TypeView.of(container, ruleSource.inners(), ruleSource.symbols(),
                ruleSource.kinds(), ruleSource.sums());
        if (!(view.shape() instanceof Shape.Sequence holding)) {
            // A total is taken of a container, and what is declared at the root is not one. Which is
            // a term nobody should have been able to build; said here rather than by composing a
            // value of whatever shape is there.
            return none(Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
        }
        // Where the rules leave nothing there is no run to spread a total over, and no element of one
        // to place. Both numbers are asked — how many the container holds and where its occurrences
        // run — because either of them left nothing settles the item, and said as a range either
        // would be the widest answer there is out of rules that admit none.
        DeclaredBounds.CountRange howMany =
                howMany(view, target.writeRoot(), within, reading, alsoHolding);
        if (howMany == null
                || !(within.projectionOf(new NumericTerm.ValueOf(occurring))
                        instanceof NumericDomain.FormProjection.Within(
                                NumericDomain.Bounds runs))) {
            return none(Generator.UnresolvedCombination.Reason.NO_VALUE_CAN_STAND_THERE);
        }
        Ends ends = Ends.of(runs == null ? NumericDomain.Bounds.OPEN : runs, elements);
        if (ends == null) {
            // Nowhere for an element to stand. Which is the rules leaving the elements nothing, and
            // is said as a container this composed none of rather than as a total nothing reaches.
            return none(Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
        }
        // A value asked at the position each element's share is written at, or around it, is that
        // position asked two things: the share and the value. One element holds one of them there,
        // and which would be whichever the composing read first, so neither is offered.
        TermPath share = underTheCasesNamed(occurring, inside.required());
        for (TermPath asked : inside.among().keySet()) {
            TermPath spelled = underTheCasesNamed(asked, inside.required());
            if (spelled.isAtOrUnder(share) || share.isAtOrUnder(spelled)) {
                return new TermRealizations.Realization.None(
                        Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE,
                        "`" + asked + "` is asked for a value where each element holds its share"
                                + " of the total");
            }
        }
        // How a value of the element is built with the number written where the total reads it,
        // asked of the plan and once per way down. A sum puts nothing under it until a case is
        // named, so what comes back is one way per case and the walk offers each of them.
        KeptApart apart = KeptApart.of(view, keptApart, holding.element(),
                target.writeRoot().element(), occurring, inside.required(), reading);
        Ways ways = waysDown(holding.element(), target.writeRoot().element(), occurring,
                inside, apart, reading);
        // Nothing to fill a container along, so there is no count and no shape of one to try. Said
        // before the counts are walked rather than as a condition on each figure below: a figure
        // reached where no container could have been built either way is one raising takes nothing
        // away from, and the walks below are what the figures are about.
        if (ways.filled().isEmpty()) {
            return ways.cutBy().isEmpty()
                    ? new TermRealizations.Realization.None(
                            Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE,
                            ways.said(occurring))
                    : new TermRealizations.Realization.Stopped(
                            CompositionShortfall.of(ways.cutBy()));
        }
        WhatWasLeft left = new WhatWasLeft();
        if (solved != null && solved.ofOneCase()) {
            left.notAllOf(CompositionRepertoire.MIXES_OF_CASES_A_TOTAL_IS_SPREAD_OVER);
        }
        // What the planning gave up at, which is a way that was there to try and was not. A way down
        // that was never planned is a value never composed, and a reader told only that nothing was
        // composed would look for the rule that refuses it.
        for (CompositionBudget cut : ways.cutBy()) {
            left.refused(cut);
        }
        WhatIsOffered offered = new WhatIsOffered();
        Makings makings = new Makings(total.at(), ends, holding, view, elements, ways, apart,
                reading, solved);
        // Every count the rules leave, which are all the counts there are: what the container may
        // hold is what the rules say, so a walk that runs out of them has run out of the population
        // and not only of what this compiler writes.
        asFarAs(countsAdmitted(howMany, alsoHolding),
                new HowManyElements(makings, offered, left), left);
        List<FixtureTemplate> built = offered.built();
        if (!built.isEmpty()) {
            return new TermRealizations.Realization.Built(built, left.shortfall());
        }
        // Nothing was composed, and what a reader may make of that is what these three say. A
        // figure that refused a candidate is why nothing came of it and is somebody's to raise; a
        // population this walks some of leaves an emptiness nothing established; a number this
        // could not hold leaves the same emptiness for a third reason, neither a figure nor a
        // population. Where there is none of them, what this looked at was everything it could have.
        CompositionShortfall met = left.shortfall();
        if (!met.figures().isEmpty()) {
            return new TermRealizations.Realization.Stopped(met);
        }
        if (!met.nothing()) {
            return new TermRealizations.Realization.Unexhausted(met, ways.said(occurring));
        }
        return new TermRealizations.Realization.None(
                Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE,
                ways.said(occurring));
    }

    /**
     * What the walks over one total left behind, which is two facts and not one.
     *
     * <p>A figure that refused a piece and a population this walks some of are different things to
     * know, and they are held in different vocabularies so that nothing downstream can put them in
     * one set. The first is somebody's to raise; raising anything reaches none of the second.
     *
     * <p>Both leave an offer that is not the whole of what there is, which is the one thing they
     * have in common and the reason both travel. A reader told every value was refused, on an offer
     * that was never everything, has been handed a sentence to act on that nothing here established.
     */
    static final class WhatWasLeft {

        private final Set<CompositionBudget> refused = EnumSet.noneOf(CompositionBudget.class);
        private final Set<CompositionRepertoire> notAllOf =
                EnumSet.noneOf(CompositionRepertoire.class);
        private final Set<CompositionCapacity> unheld = new HashSet<>();

        /** A piece was in front of a walk and this figure left no room for it. */
        void refused(CompositionBudget figure) {
            refused.add(figure);
        }

        /** A walk over this population went everywhere it knows how to, which was not everywhere. */
        void notAllOf(CompositionRepertoire population) {
            notAllOf.add(population);
        }

        /** A number this walk needed could not be held, which is neither of the other two: no
         *  figure stopped it and no population is somebody's to write the rest of — a host with
         *  more room reaches it or nothing does. */
        void unheld(CompositionCapacity capacity) {
            unheld.add(capacity);
        }

        /** The figures that refused a piece, which are the ones a composing was stopped by. */
        Set<CompositionBudget> refused() {
            return Set.copyOf(refused);
        }

        /** The populations an offer made under these walks holds some of and not all of. */
        Set<CompositionRepertoire> notAllOf() {
            return Set.copyOf(notAllOf);
        }

        /** The numbers a walk worked out and could not hold. */
        Set<CompositionCapacity> unheld() {
            return Set.copyOf(unheld);
        }

        /**
         * What building a piece met before it could be put in front of a walk — a value beside
         * the number past what a proposal holds — in whichever of the vocabularies it is.
         */
        void met(CompositionShortfall shortfall) {
            refused.addAll(shortfall.figures());
            notAllOf.addAll(shortfall.populations());
            unheld.addAll(shortfall.unheld());
        }

        /** All of it, as the one shortfall a realization carries on. */
        CompositionShortfall shortfall() {
            return CompositionShortfall.of(refused, notAllOf, unheld);
        }
    }

    /**
     * A consumer that does as many pieces as one figure of this compiler's leaves it room for.
     *
     * <p>{@link Taken#NOT_TAKEN} only where {@link #figure()} leaves no room for the piece in front
     * of it. That is the whole of what this adds to {@link Taking}: a walk reads the refusal as the
     * figure being reached, so a consumer refusing a piece for any other reason would file its own
     * answer under somebody else's number.
     *
     * <p>And the room is worked out from {@link #figure()} rather than from a number beside it.
     * Read from a second place, what the consumer has room for and what it reports having run out of
     * are two declarations of one policy, and they part the first time one is raised.
     */
    interface Spending<T> extends Taking<T> {

        /** The figure this has no room past. */
        CompositionBudget figure();
    }

    /**
     * Every piece to the consumer, and the figure where the walk was left holding one.
     *
     * <p><b>The one place a figure is recorded.</b> A piece the consumer would not do is a piece
     * this was holding, which is what makes the figure a search declining to go on rather than a
     * property of how the search was set up. Worked out anywhere else, the record is a reading of
     * the arrangement — an unbounded container always has counts above the figure, so a walk that
     * asked whether it had them said a figure had been reached before trying anything.
     *
     * <p>Nothing is said here about whether the pieces were the whole of their kind. That is not
     * something a walk over them can see, and it is not a figure: what it takes to reach the rest
     * of a population is somebody writing the rest, so it is claimed and shown where the pieces are
     * chosen ({@link CompositionRepertoire}).
     *
     * <p>What a caller does with {@link Traversal#SATISFIED} is its own. It is not this walk that
     * left something: a consumer that has what it came for says so, and where that is because a
     * walk further in stopped, that walk has already recorded its figure here.
     */
    static <T> Traversal asFarAs(Iterable<T> pieces, Spending<T> doing, WhatWasLeft left) {
        for (T each : pieces) {
            switch (doing.take(each)) {
                case NOT_TAKEN -> {
                    left.refused(doing.figure());
                    return Traversal.STOPPED;
                }
                case AND_DONE -> {
                    return Traversal.SATISFIED;
                }
                case AND_MORE -> { }
            }
        }
        return Traversal.EXHAUSTED;
    }

    /**
     * The counts the rules leave the container, from the least of them upward.
     *
     * <p>All of them and not the ones a figure allows. What bounds this walk is the consumer, which
     * is handed a count and answers whether it has room for one that size — so the count that is
     * refused is a count the rules admit, and cutting the list to the figure first would leave
     * nothing for it to refuse.
     *
     * <p>Which is also what ends this where the rules cap nothing. A range the rules leave open at
     * the top runs to the largest count there is, and what stops the walk before then is the
     * consumer having no room, as it is at every other length.
     */
    static Iterable<Integer> countsAdmitted(DeclaredBounds.CountRange howMany,
                                                    HowManyIsAskedFor alsoHolding) {
        int from = Math.max(howMany.least(), 0);
        return () -> new Iterator<>() {

            private int at = from;

            @Override
            public boolean hasNext() {
                // Past the sizes the group asks for as well as past the ones the rules leave. A
                // size some other number of the same location refuses is no candidate at all, so
                // it is stepped over here rather than handed on and refused — the figure below
                // counts what it was handed, and a count nobody asked for would spend it.
                while (at <= howMany.most() && !asked(at)) {
                    at++;
                }
                return at <= howMany.most();
            }

            @Override
            public Integer next() {
                if (!hasNext()) {
                    throw new NoSuchElementException();
                }
                return at++;
            }

            private boolean asked(int many) {
                return alsoHolding == null || alsoHolding.holds(many);
            }
        };
    }

    /**
     * How many a container is asked to hold, where that is asked beside what it comes to.
     *
     * <p>The set and the order it is a set of places on, because membership is the set's to answer
     * and it answers it against the order — {@link NumericSet#holds}. Held as a pair for that
     * reason: a caller passing the set alone would leave every reader of it choosing an order, and
     * the one they would choose is the one in front of them.
     *
     * @param wanted  the numbers the rules leave how many it holds
     * @param counted the order those numbers are places of
     */
    record HowManyIsAskedFor(NumericSet wanted, Carrier counted) {

        HowManyIsAskedFor {
            Objects.requireNonNull(wanted, "how many it is asked to hold is a set of counts");
            Objects.requireNonNull(counted, "a count is a place on the order it is counted by");
        }

        /** Whether holding that many is one of the numbers asked for. */
        boolean holds(int many) {
            return wanted.holds(new Count(BigDecimal.valueOf(many)), counted);
        }

        /** As ends, for the walk that steps the counts. */
        NumericDomain.Bounds extent() {
            return wanted.extent();
        }
    }

    /**
     * The makings of one container: where its elements stand, what holds them and how to fill them.
     *
     * <p>Everything about the total that neither of the walks below changes. Held together because
     * both of them fill from it and neither owns it — the counts walk hands a size to the shapes
     * walk, and what a shape of that size is made of is the same either way down.
     *
     * @param total     the number the elements are to come to
     * @param container the position the container stands at, read once and worn by what is built
     * @param apart     what the rules keep its elements apart at
     * @param solved    where the total is of what a walk computed of each element, the one field
     *                  that is chosen and solved for; null where the total is of what the elements
     *                  hold
     */
    private record Makings(BigDecimal total, Ends ends, Shape.Sequence holding, TypeView container,
                           Carrier elements, Ways ways, KeptApart apart,
                           RuleReadingContext reading, FieldSolved solved) {}

    /**
     * The one field of each element a total of what a walk computed of it is solved for.
     *
     * <p>A computation that is a form of one field — {@code weight·field + constant} — comes to a
     * total of {@code weight·Σfield + many·constant}, so for each count the fields are to add up to
     * what that leaves after the constants are taken off and the weight divided out. The elements
     * are then chosen exactly as for a total of the field itself, on the field's own order and under
     * the rules that bound it.
     *
     * <p>Only a form of one field. With a second, what one element's number is depends on a value
     * nothing here chooses, and solving for the first would be solving against a guess at the
     * second.
     *
     * <p>A choice by case is solved for through each arm whose answer is a form of one field of the
     * case it took ({@link #throughEach}). The field stands under the case, so every element written
     * to hold it is of that case and is taken by that arm, and its number is that arm's form. Those
     * are some of the containers the total is over and not all of them — one mixing the cases is
     * never written — which is said beside whatever is written.
     *
     * <p>A choice by the position between a form of one field and a number of none is solved for
     * the same way at the positions that take the form ({@link Kept}): those carry the field and the
     * total, and the rest stand at the field's start and add their number whatever they hold. A
     * total of the first elements, or of those from an index on, is that.
     *
     * @param field     where each element's field stands
     * @param carrier   the order the field's values are written on
     * @param weight    what the field is multiplied by, never nought
     * @param constant  what each element's number has beside it
     * @param ofOneCase whether the elements written are all of one case of several the computation
     *                  chooses among
     * @param kept      the positions that take the form, where a choice by the position chose it;
     *                  null where every element does
     */
    private record FieldSolved(TermPath field, Carrier carrier, ExactRatio weight,
                               ExactRatio constant, boolean ofOneCase, Kept kept) {

        /**
         * The positions of a container that take the form a total is solved through, and what the
         * rest come to.
         *
         * @param test      the test of a position that takes the form
         * @param direction which end the positions are counted from
         * @param rest      what the number of an element at any other position is
         */
        record Kept(ElementValue.PositionTest test, TraversalDirection direction,
                    ExactRatio rest) {}

        /** Every field a computation is solved for: the one field of a form, each arm's of a
         *  choice by case, the form's of a choice by the position between it and a number, and
         *  none where it is none of these. */
        static List<FieldSolved> of(RunSource.ComputedOccurrences run, TermOrders orders) {
            List<FieldSolved> out = new ArrayList<>();
            switch (run.computation()) {
                case ElementValue.Affine affine -> {
                    FieldSolved solved = ofAForm(affine, null, run, orders);
                    if (solved != null) {
                        out.add(solved);
                    }
                }
                case ElementValue.OfItsCase choice -> {
                    for (ElementValue.OfItsCase.Arm arm : choice.arms()) {
                        if (arm.value() instanceof ElementValue.Affine affine) {
                            FieldSolved solved = ofAForm(affine, choice.taken(arm), run, orders);
                            if (solved != null) {
                                out.add(solved);
                            }
                        }
                    }
                }
                case ElementValue.ByPosition choice -> {
                    FieldSolved solved = byPosition(choice, run, orders);
                    if (solved != null) {
                        out.add(solved);
                    }
                }
                // A choice by a flag chooses per element on a value nothing here chooses, and a
                // weight made of the position, or a choice between two forms of the field, weighs
                // each position apart: the fields adding up to a total are no one quotient of it.
                case ElementValue.Choose _, ElementValue.Indexed _,
                     ElementValue.SumOfChoices _ -> { }
            }
            return List.copyOf(out);
        }

        /**
         * The field a choice by the position is solved for, where one of its answers is a form of
         * one field and the other a number of none — or null where it is any other choice.
         *
         * <p>Two forms of the field weigh the positions apart, and a choice inside a choice is a
         * test of a test; neither is a run of positions carrying one form.
         */
        private static FieldSolved byPosition(ElementValue.ByPosition choice,
                                              RunSource.ComputedOccurrences run,
                                              TermOrders orders) {
            if (!(choice.whenHolds() instanceof ElementValue.Affine holds)
                    || !(choice.otherwise() instanceof ElementValue.Affine not)) {
                return null;
            }
            boolean formWhereItHolds = not.form().coefs().isEmpty();
            ElementValue.Affine form = formWhereItHolds ? holds : not;
            ElementValue.Affine rest = formWhereItHolds ? not : holds;
            if (!rest.form().coefs().isEmpty()) {
                return null;
            }
            FieldSolved solved = ofAForm(form, null, run, orders);
            return solved == null ? null
                    : new FieldSolved(solved.field(), solved.carrier(), solved.weight(),
                            solved.constant(), false, new Kept(
                                    formWhereItHolds ? choice.test() : choice.test().denied(),
                                    run.order().direction(), rest.form().constant()));
        }

        /** The field {@code affine} is solved for, where it is a form of one field and, under an
         *  arm, a field of the case the arm {@code taken} — or null. */
        private static FieldSolved ofAForm(ElementValue.Affine affine, ElementProjection taken,
                                           RunSource.ComputedOccurrences run, TermOrders orders) {
            if (affine.form().coefs().size() != 1) {
                return null;
            }
            Map.Entry<ElementProjection, ExactRatio> only =
                    affine.form().coefs().entrySet().iterator().next();
            TermPath field = only.getKey().from(run.elements());
            if (taken != null && !field.isAtOrUnder(taken.from(run.elements()))) {
                return null;
            }
            Carrier carrier = orders.fieldCarrier(only.getKey());
            return carrier == null ? null
                    : new FieldSolved(field, carrier, only.getValue(), affine.form().constant(),
                            taken != null, null);
        }

        /** How many of {@code many} elements carry the field the total is solved through: every
         *  one, or the ones at the positions {@link #kept} names. */
        int carrying(int many) {
            if (kept == null) {
                return many;
            }
            int carrying = 0;
            for (int position = 0; position < many; position++) {
                if (kept.test().holdsOf(position)) {
                    carrying++;
                }
            }
            return carrying;
        }

        /**
         * What the fields of the elements carrying it, of a container of {@code many}, are to add
         * up to for the numbers computed of every element to add up to {@code total}, or why that
         * number is not held.
         *
         * <p>Empty where it is no written decimal: the fields are decimals and their sum is one, so
         * no container of that many comes to the total.
         */
        ExactAnswer<Optional<BigDecimal>> fieldsAddingUpTo(BigDecimal total, int many) {
            int carrying = carrying(many);
            ExactRatio rest = kept == null ? ExactRatio.ZERO : kept.rest();
            return constant.times(ExactRatio.of(carrying))
                    .flatMap(carried -> rest.times(ExactRatio.of(many - carrying))
                            .flatMap(carried::plus))
                    .flatMap(constants -> ExactRatio.of(total).minus(constants))
                    .flatMap(remains -> remains.dividedBy(weight))
                    .flatMap(ExactRatio::writtenDecimal);
        }

        /**
         * The values of a container of {@code many}, in the order the row writes them: the shares
         * {@code split} at the positions that carry the field, counted from the end the positions
         * are counted from, and {@code free} at the rest.
         */
        List<BigDecimal> placed(List<BigDecimal> split, int many, BigDecimal free) {
            if (kept == null) {
                return split;
            }
            List<BigDecimal> written = new ArrayList<>(Collections.nCopies(many, free));
            Iterator<BigDecimal> shares = split.iterator();
            for (int position = 0; position < many; position++) {
                if (kept.test().holdsOf(position)) {
                    written.set(kept.direction() == TraversalDirection.FORWARD
                            ? position : many - 1 - position, shares.next());
                }
            }
            return List.copyOf(written);
        }
    }

    /**
     * How many elements the container is filled with, walked from the least the rules leave upward.
     *
     * <p>The figure is on the count and not on how many counts were tried. What it says is how many
     * elements a row is worth carrying, so a count past it is a count with no room whatever came
     * before it — and a walk counting its own steps would have taken sixty-four counts from a rule
     * that starts at a hundred.
     *
     * <p>Its shapes are a walk of their own at every count. Held as one across the counts, the
     * figure would be how many decompositions the whole total is offered in rather than how many one
     * count is spread as, which is a different policy nobody wrote down.
     */
    private static final class HowManyElements implements Spending<Integer> {

        private final Makings makings;
        private final WhatIsOffered offered;
        private final WhatWasLeft left;

        HowManyElements(Makings makings, WhatIsOffered offered, WhatWasLeft left) {
            this.makings = makings;
            this.offered = offered;
            this.left = left;
        }

        @Override
        public Taken take(Integer many) {
            if (many > figure().maximum()) {
                return Taken.NOT_TAKEN;
            }
            BigDecimal total = makings.total();
            FieldSolved solved = makings.solved();
            int carrying = solved == null ? many : solved.carrying(many);
            // The elements that carry no share stand at the start and are one of the values each
            // could hold; where every element is to be apart from every other, those alike are
            // apart from nothing and the count is one this writes none of.
            if (carrying < many) {
                left.notAllOf(CompositionRepertoire.WAYS_A_TOTAL_IS_SPREAD);
                if (makings.apart().numbersApart()) {
                    return Taken.AND_MORE;
                }
            }
            if (solved != null) {
                switch (makings.solved().fieldsAddingUpTo(total, many)) {
                    case ExactAnswer.Unheld<Optional<BigDecimal>> unheld -> {
                        left.unheld(new CompositionCapacity(
                                CompositionCapacity.Where.VALUES_A_TOTAL_IS_SPREAD_OVER,
                                unheld.why()));
                        return Taken.AND_MORE;
                    }
                    case ExactAnswer.Held<Optional<BigDecimal>> held -> {
                        if (held.value().isEmpty()) {
                            return Taken.AND_MORE;
                        }
                        total = held.value().get();
                    }
                }
            }
            // Said of the shapes this count is spread in, before any of them is walked, because it
            // is about which arrangements there are rather than about what came of trying two of
            // them. Nothing bounds this loop but the shapes there are to write, so a shape is never
            // refused here and no figure of this compiler's is reached by spreading.
            if (!coversEveryArrangement(carrying, total)) {
                left.notAllOf(CompositionRepertoire.WAYS_A_TOTAL_IS_SPREAD);
            }
            for (Spread how : Spread.values()) {
                switch (splitting(total, carrying, makings.ends(), how, makings.elements(),
                        makings.apart().numbersApart())) {
                    case Split.None _ -> { }
                    // Its own vocabulary and not `notAllOf`: this compiler has a way of generating
                    // every other arrangement of this shape and reached for it, and what stopped it
                    // is the arithmetic rather than a shape this compiler cannot produce. Told apart
                    // so that raising the figure `MORE_ROOM_COULD_ANSWER` names reaches this, where
                    // `WAYS_A_TOTAL_IS_SPREAD` would tell a reader nobody can raise anything.
                    case Split.NotWorkedOut(UnheldNumber why) ->
                            left.unheld(new CompositionCapacity(
                                    CompositionCapacity.Where.VALUES_A_TOTAL_IS_SPREAD_OVER, why));
                    case Split.Some(List<BigDecimal> values) -> {
                        // Every way down at this count, and the whole container by one of them.
                        // Which case an element is is a fact about the value, so a container whose
                        // elements are of several would be offering a shape nothing asked for; what
                        // the walk owes is to offer each case and to say the rest were never made.
                        //
                        // An offer with no room for another container has none at any count, so
                        // this is the end of the counts as well and not only of the shapes.
                        List<BigDecimal> written = solved == null ? values
                                : solved.placed(values, many, makings.ends().from().at());
                        if (asFarAs(containers(written), offered, left) == Traversal.STOPPED) {
                            return Taken.AND_DONE;
                        }
                    }
                }
            }
            return Taken.AND_MORE;
        }

        /**
         * The containers this split fills, one per way down that builds one.
         *
         * <p>Built as the walk asks for them. Made in a list first, the ways after the one that
         * filled the offer would be values composed for nobody, which is work at exactly the moment
         * this compiler has said it will do no more.
         */
        private Iterable<FixtureTemplate> containers(List<BigDecimal> split) {
            return () -> makings.ways().filled().stream()
                    .map(each -> filled(split, makings.holding(), makings.container(), each,
                            makings.apart(), makings.elements(), makings.reading()))
                    .<FixtureTemplate>mapMulti((built, out) -> {
                        left.met(built.met());
                        built.values().forEach(out);
                    })
                    .iterator();
        }

        /**
         * Whether the shapes written here are every arrangement of this many elements there is.
         *
         * <p><b>Shown, or not said.</b> An offer that claims to hold every way of reaching the
         * total is a claim about all the arrangements, and two shapes are two of the many — so this
         * answers for the counts where the many are provably not more than two, and every other
         * count is one this walks some of.
         *
         * <p>Two showings, and both are arithmetic on what the elements stand on. A count of one
         * takes the whole of the difference and a count of nought takes none of it, so there is the
         * one arrangement either way and both shapes are it. And where every element moved as far
         * as its order allows still does not reach the total, no arrangement of that many does —
         * the shapes cover the arrangements by there being none of them.
         *
         * <p>Which way it errs is the whole point. A count whose arrangements this does happen to
         * cover is walked as one it does not, and an offer says it holds less than it does; the
         * other way round, a reader is told every value was refused by a walk that never wrote most
         * of them.
         */
        private boolean coversEveryArrangement(int many, BigDecimal total) {
            return many <= 1 || !makings.ends().reaches(total, many);
        }

        @Override
        public CompositionBudget figure() {
            return CompositionBudget.ELEMENTS_A_TOTAL_IS_SPREAD_OVER;
        }
    }

    /**
     * The containers offered for the total, as many of them as the figure is written at.
     *
     * <p>A container alike to one already offered is not another of them, and it is not a piece this
     * had no room for either: what the figure counts is what a reader is handed, and a walk that met
     * the figure on a repeat would name it having refused nothing.
     */
    static final class WhatIsOffered implements Spending<FixtureTemplate> {

        private final List<FixtureTemplate> built = new ArrayList<>();

        @Override
        public Taken take(FixtureTemplate one) {
            if (built.contains(one)) {
                return Taken.AND_MORE;
            }
            if (built.size() == figure().maximum()) {
                return Taken.NOT_TAKEN;
            }
            built.add(one);
            return Taken.AND_MORE;
        }

        /** What was offered, in the order it was built. */
        List<FixtureTemplate> built() {
            return List.copyOf(built);
        }

        @Override
        public CompositionBudget figure() {
            return CompositionBudget.SHAPES_OF_A_TOTAL_OFFERED;
        }
    }

    /**
     * How many the container may hold, by the rules and by what reaches the point.
     *
     * <p>Both, and the tighter of them. What the declarations say about a type is one rule and what
     * a record says about the field holding it is another, and a container built against either
     * alone is refused by the other — a rule asking a ledger for two lines is written where the
     * ledger is, and a reading that knew only {@code List<Item>} would offer one.
     *
     * <p>The second is asked of the region rather than read out of the declarations a second time.
     * How many a location holds is a number like any other, so the region already answers it, and it
     * answers it as narrowed by whatever the row had to pass to get here. Read here instead, this
     * would be a second reading of the rules, free to part from the one the search was run against.
     */
    static DeclaredBounds.CountRange howMany(TypeView container, TermPath root,
                                                     SearchRegion within,
                                                     RuleReadingContext reading,
                                                     HowManyIsAskedFor alsoHolding) {
        DeclaredBounds.CountRange declared = narrowed(
                DeclaredBounds.countsHeld(container, reading, null), alsoHolding);
        NumericTerm.FromOnePosition term = countTaken(container, root, reading);
        if (term == null) {
            return declared;
        }
        // What the rules leave on top of what the declarations do, and null where they leave it
        // nothing at all. Answered as a range there, what the rules settle would come back as the
        // declarations' own range — which is wider than what holds, and the widening is what sends a
        // search off to fill a container the model admits none of.
        return switch (within.projectionOf(term)) {
            case NumericDomain.FormProjection.NothingIsLeft _ -> null;
            case null -> declared;
            case NumericDomain.FormProjection.Within(NumericDomain.Bounds runs) ->
                    runs == null ? declared : new DeclaredBounds.CountRange(
                            Math.max(declared.least(), CountDomain.leastFrom(runs.min())),
                            Math.min(declared.most(), CountDomain.mostFrom(runs.max())));
        };
    }

    /**
     * The same range, no wider than the ends of what a group of numbers asks of the size.
     *
     * <p>The ends only. Which sizes inside them are asked for is the set's answer and is asked of
     * each count as it is stepped, the way every walk here narrows first and decides after
     * ({@link NumericSet#extent()} beside {@link NumericSet#holds}) — a set with holes in it has no
     * pair of ends that says which they are.
     */
    private static DeclaredBounds.CountRange narrowed(DeclaredBounds.CountRange range,
                                                      HowManyIsAskedFor alsoHolding) {
        if (alsoHolding == null) {
            return range;
        }
        NumericDomain.Bounds asked = alsoHolding.extent();
        return new DeclaredBounds.CountRange(
                Math.max(range.least(), CountDomain.leastFrom(asked.min())),
                Math.min(range.most(), CountDomain.mostFrom(asked.max())));
    }

    /** The number the rules count this container by, or null where nothing counts it. */
    private static NumericTerm.FromOnePosition countTaken(TypeView container, TermPath root,
                                                          RuleReadingContext reading) {
        ValueName.Stdlib counts =
                NumericMeasures.takenOf(container.declared(), reading.source().inners());
        return counts == null ? null
                : NumericTerm.TakenOf.asItStands(counts, root, container.declared(),
                        reading.source().inners(), reading.source().symbols());
    }

    /**
     * The path whose occurrences inside the root are added up.
     *
     * <p>The element itself where the total is of what a location holds, and the run's own path
     * where it is over a run. One question about two terms and not two questions: what is added up
     * is what stands at a path under the container, and where the path stops is the whole
     * difference.
     *
     * <p>Asked of the number and not of the target it is realized by. What is added up is read
     * where the rules name it, and where a row writes to move it is another question with another
     * owner ({@link RealizationTarget#writeRoot}) — so a way of writing a number added later is not
     * a second answer about which occurrences a container counts.
     */
    private static TermPath occurrences(RealizationTarget.OfANumber target) {
        return switch (target.term()) {
            case NumericTerm.FromOnePosition one -> one.position().element();
            case NumericTerm.TakenOver over -> over.source().subjectPath();
            // How often a value occurs is no total of what the elements hold, and is composed by
            // choosing which elements repeat ({@link CardinalityComposer#composeAlike}).
            case NumericTerm.Multiplicity among -> throw new IllegalStateException(
                    among + " is composed by repeating elements, and nothing here adds it up");
            case NumericTerm.OccurrencesOfItsValue among -> throw new IllegalStateException(
                    among + " is composed by repeating values across containers, and nothing here"
                            + " adds it up");
            case NumericTerm.OccurrencesOfAKey ofAKey -> throw new IllegalStateException(
                    ofAKey + " is composed by repeating a value across containers, and nothing"
                            + " here adds it up");
            case NumericTerm.ExtremeOfItsKey extreme -> throw new IllegalStateException(
                    extreme + " is written as one value, and nothing here adds it up");
        };
    }

    /**
     * How the difference between a starting point and the total is spread over the elements.
     *
     * <p>Two, because the shapes a decomposition can take are what the rules the elements are under
     * tell apart. A rule taking one number out of the middle of a run refuses the container that put
     * the whole difference on one element and admits the one that shared it, and neither shape is
     * more of a decomposition than the other. What is not here is a search: these are two of the
     * many, and what the walk owes is to say that the rest were never made.
     */
    enum Spread {

        /** The whole difference on as few elements as will carry it, the rest where they started. */
        MASSED,

        /** As near an equal share each as the order allows, the last taking what division left. */
        LEVEL
    }

    /**
     * What sharing a total out over {@code many} elements one {@link Spread} came to.
     *
     * <p>Three, and not a nullable list: a shape that reaches no decomposition and a shape the
     * exact arithmetic could not work out are different facts, and a walk reading them alike would
     * call an arithmetic gap a proof that no arrangement exists — which is the one thing
     * {@link ExactAnswer} exists to keep a caller from doing by accident.
     */
    sealed interface Split {

        /** This shape reaches no decomposition. Not that none exists — another shape or another
         *  count may — and the walk that asked says so. */
        record None() implements Split {}

        /** Every value along the way arrived, and one of them is a number the exact arithmetic
         *  could not hold. Never read as {@link None}: this shape's existence is undecided, not
         *  refused. */
        record NotWorkedOut(UnheldNumber why) implements Split {}

        record Some(List<BigDecimal> values) implements Split {}
    }

    /**
     * The numbers {@code many} elements hold for the container to come to {@code total}, by one
     * {@link Spread}.
     *
     * <p>Every element starts where {@link Ends#from} puts it and moves by its share of what is
     * still owed. <b>Either way along the order</b>: a total below where the elements start is
     * reached by moving down as readily as one above it is reached by moving up, and a run open
     * below or held away from a value has no least element to start from at all. Read as a floor,
     * the start was a floor only for the ranges that have one — and a list of whole numbers had no
     * container coming to less than nothing.
     *
     * <p>How far one element may move is the distance to the end it is moving toward, and nothing at
     * all where that end names no value: an order open that way, or a dense one held away from a
     * value it excludes, has no number to move up to. What comes of that is put back to the range
     * and to the carrier, which is what makes a start that is not the least, and a distance that is
     * not a bound, safe to work with.
     *
     * <p>Null where this shape reaches no decomposition. Which is not that none exists — another
     * shape or another count may — and the walk that asked says so.
     */
    static Split splitting(BigDecimal total, int many, Ends ends, Spread how,
                           Carrier elements) {
        if (many == 0) {
            return total.signum() == 0 ? new Split.Some(List.of()) : new Split.None();
        }
        // No element moves further than the end it is heading for, and what is owed shrinks toward
        // nothing without changing sign, so a total past what that many reach together is one the
        // walk below would end owing something on. Asked first, since a walk up the counts meets
        // every count past the last that reaches, and each would otherwise be walked to its end.
        if (!ends.reaches(total, many)) {
            return new Split.None();
        }
        // Held in ratios throughout the sharing out, and narrowed to a written decimal only where an
        // element's own value is built. Every step below that can go unheld says so as
        // {@link Split.NotWorkedOut} rather than {@link Split.None}: a shape the exact arithmetic
        // could not finish is not a shape this compiler has ruled out, and reading the two alike is
        // exactly the confusion {@link ExactAnswer} exists to keep a caller from making by accident.
        ExactRatio from = ends.from().exactly();
        ExactAnswer<ExactRatio> started = from.times(ExactRatio.of(many))
                .flatMap(counted -> ExactRatio.of(total).minus(counted));
        if (started instanceof ExactAnswer.Unheld<ExactRatio> unheldStart) {
            return new Split.NotWorkedOut(unheldStart.why());
        }
        ExactRatio owed = ((ExactAnswer.Held<ExactRatio>) started).value();
        // How many places a dense share is rounded to: the most the numbers taking part in the
        // sharing were written to, and at least one. Read off the written numbers themselves — the
        // total and the counts the ends hold — and never off `owed`, which as an exact ratio holds
        // the number and not the places. It starts at the total and the start, and an end joins it
        // only where the loop below actually moves a share to that end: an end nothing reaches
        // takes no part in the sharing, so its places are not the sharing's.
        int scale = Math.max(Math.max(total.scale(), ends.from().at().scale()), 1);
        List<BigDecimal> split = new ArrayList<>();
        for (int i = 0; i < many; i++) {
            ExactRatio wanted;
            if (how == Spread.MASSED) {
                wanted = owed;
            } else {
                ExactAnswer<ExactRatio> sharedAnswer = shared(owed, scale, many - i, elements);
                if (sharedAnswer instanceof ExactAnswer.Unheld<ExactRatio> unheldShared) {
                    return new Split.NotWorkedOut(unheldShared.why());
                }
                wanted = ((ExactAnswer.Held<ExactRatio>) sharedAnswer).value();
            }
            ExactAnswer<ExactRatio> addAnswer = toward(wanted, ends);
            if (addAnswer instanceof ExactAnswer.Unheld<ExactRatio> unheldAdd) {
                return new Split.NotWorkedOut(unheldAdd.why());
            }
            ExactRatio add = ((ExactAnswer.Held<ExactRatio>) addAnswer).value();
            // Moved to the end it was heading for exactly where `add` is not the share it asked
            // for, and only then is that end one of the numbers the sharing is made of. Never null
            // here: an end that names no value never holds a share back.
            if (add.compareTo(wanted) != 0) {
                Count reached = wanted.signum() >= 0 ? ends.upTo() : ends.downTo();
                scale = Math.max(scale, reached.at().scale());
            }
            ExactAnswer<ExactRatio> atAnswer = from.plus(add);
            if (atAnswer instanceof ExactAnswer.Unheld<ExactRatio> unheldAt) {
                return new Split.NotWorkedOut(unheldAt.why());
            }
            ExactAnswer<Optional<BigDecimal>> written =
                    ((ExactAnswer.Held<ExactRatio>) atAnswer).value().writtenDecimal();
            if (written instanceof ExactAnswer.Unheld<Optional<BigDecimal>> unheldWritten) {
                return new Split.NotWorkedOut(unheldWritten.why());
            }
            BigDecimal at = ((ExactAnswer.Held<Optional<BigDecimal>>) written).value()
                    .orElse(null);
            if (at == null) {
                return new Split.NotWorkedOut(UnheldNumber.NO_REPRESENTATION_EXISTS);
            }
            // Put back to the rules and to the carrier, which are the two things a number has to be
            // to be a value here. Where an element starts and how far it may be moved are worked out
            // from the ends and are this reader's arithmetic; whether what came of them is a value
            // is not, and a decomposition that reads its own workings back would be sound only for
            // as long as the workings are. This is the one place a proof of {@link Split.None} is
            // actually earned: every number above held, and the rules or the carrier still refuse it.
            if (!ends.runs().admits(Count.of(at))
                    || !(elements.onTheGrid(Count.of(at)) instanceof Count on)
                    || on.at().compareTo(at) != 0) {
                return new Split.None();
            }
            split.add(at);
            ExactAnswer<ExactRatio> nextOwed = owed.minus(add);
            if (nextOwed instanceof ExactAnswer.Unheld<ExactRatio> unheldNext) {
                return new Split.NotWorkedOut(unheldNext.why());
            }
            owed = ((ExactAnswer.Held<ExactRatio>) nextOwed).value();
        }
        return owed.isZero() ? new Split.Some(List.copyOf(split)) : new Split.None();
    }

    /**
     * The same, with no two of the numbers alike where {@code apart} says the elements are kept
     * apart by what they hold there ({@link KeptApart#numbersApart}).
     */
    static Split splitting(BigDecimal total, int many, Ends ends, Spread how, Carrier elements,
                           boolean apart) {
        return apart ? splittingApart(total, many, ends, how, elements)
                : splitting(total, many, ends, how, elements);
    }

    /**
     * {@code many} numbers coming to {@code total} by one {@link Spread}, no two of them alike.
     *
     * <p>Spread as numbers that may repeat and then set a step apart. Numbers in ascending order no
     * two of which are alike are, with the one at each place lowered by that many steps, numbers in
     * order that may repeat — and the other way round. So the total less what the steps add, spread
     * over ends whose top is lowered by the steps the highest number is raised by, comes back as
     * numbers that may repeat, and raising each by its place in their order puts them apart. The
     * step is the carrier's: one count where it steps, and the finest place the sharing is written
     * to where it does not ({@link #splitting}).
     *
     * <p>Put back to the rules afterwards, as {@link #splitting} puts its own: a value the rules
     * hold away from inside the run is one a raised number may land on, and the shape then reaches
     * no decomposition. Worked in ratios throughout, and a number the exact arithmetic could not
     * hold is said as {@link Split.NotWorkedOut}, as there.
     */
    private static Split splittingApart(BigDecimal total, int many, Ends ends, Spread how,
                                        Carrier elements) {
        if (many <= 1) {
            return splitting(total, many, ends, how, elements);
        }
        ExactRatio step = elements.spacing() == Granularity.DISCRETE ? ExactRatio.of(1)
                : ExactRatio.of(BigDecimal.valueOf(1,
                        Math.max(Math.max(total.scale(), ends.from().at().scale()), 1)));
        Raised lowered = raisedBy(ExactRatio.of(total),
                step.times(ExactRatio.of((long) many * (many - 1) / 2)), -1);
        Raised top = ends.upTo() == null ? null
                : raisedBy(ends.upTo().exactly(), step.times(ExactRatio.of(many - 1)), -1);
        if (lowered.why() != null || (top != null && top.why() != null)) {
            return new Split.NotWorkedOut(lowered.why() != null ? lowered.why() : top.why());
        }
        Count upTo = top == null ? null : Count.of(top.at());
        if (upTo != null && ends.downTo() != null && upTo.at().compareTo(ends.downTo().at()) < 0) {
            return new Split.None();
        }
        Count from = upTo != null && ends.from().at().compareTo(upTo.at()) > 0 ? upTo : ends.from();
        Split spread = splitting(lowered.at(), many,
                new Ends(from, ends.downTo(), upTo, NumericDomain.Bounds.OPEN), how, elements);
        if (!(spread instanceof Split.Some(List<BigDecimal> values))) {
            return spread;
        }
        List<BigDecimal> inOrder = new ArrayList<>(values);
        inOrder.sort(Comparator.naturalOrder());
        List<BigDecimal> out = new ArrayList<>();
        for (int i = 0; i < inOrder.size(); i++) {
            Raised raised = raisedBy(ExactRatio.of(inOrder.get(i)),
                    step.times(ExactRatio.of(i)), 1);
            if (raised.why() != null) {
                return new Split.NotWorkedOut(raised.why());
            }
            BigDecimal at = raised.at();
            if (!ends.runs().admits(Count.of(at))
                    || !(elements.onTheGrid(Count.of(at)) instanceof Count on)
                    || on.at().compareTo(at) != 0) {
                return new Split.None();
            }
            out.add(at);
        }
        return new Split.Some(List.copyOf(out));
    }

    /** A number moved by so much, as a written decimal, or why the exact arithmetic could not hold
     *  it: exactly one of the two. */
    private record Raised(BigDecimal at, UnheldNumber why) {}

    /** {@code from} moved by {@code by} in the direction {@code sign} says. */
    private static Raised raisedBy(ExactRatio from, ExactAnswer<ExactRatio> by, int sign) {
        ExactAnswer<Optional<BigDecimal>> written = by
                .flatMap(step -> sign < 0 ? from.minus(step) : from.plus(step))
                .flatMap(ExactRatio::writtenDecimal);
        return switch (written) {
            case ExactAnswer.Unheld<Optional<BigDecimal>> unheld -> new Raised(null, unheld.why());
            case ExactAnswer.Held<Optional<BigDecimal>> held -> held.value().isPresent()
                    ? new Raised(held.value().get(), null)
                    : new Raised(null, UnheldNumber.NO_REPRESENTATION_EXISTS);
        };
    }

    /**
     * One element's share of what is still owed, over the elements still to be given one, or which
     * way the exact arithmetic could not hold it.
     *
     * <p>Toward nought, so the elements before the last take no more than their share and the last
     * takes what division left over. Which is what makes the shares add up without a remainder to
     * place: the last element is given whatever is still owed, whatever the division came to.
     *
     * <p>An order that steps divides to a whole number of its counts; one that does not is divided
     * to {@code scale} places, which {@link #splitting} tracks across the whole walk rather than
     * reading back off {@code owed} here — a share finer than that is a value the total was
     * never stated to, and one coarser than the numbers the total and the ends were themselves
     * written at is a share the decomposition never asked for either. Divided in ratios throughout:
     * {@code among} is a whole number and never nought, so the divisor never refuses, and what asks
     * the exact arithmetic something it may refuse is only the room the quotient itself needs —
     * which is {@link ExactRatio#truncated}/{@link ExactRatio#asDecimal}'s question and not
     * {@code BigDecimal.divide}'s.
     */
    private static ExactAnswer<ExactRatio> shared(ExactRatio owed, int scale, int among,
                                                   Carrier elements) {
        ExactRatio by = ExactRatio.of(among);
        if (elements.spacing() == Granularity.DISCRETE) {
            return switch (owed.dividedBy(by).flatMap(ExactRatio::truncated)) {
                case ExactAnswer.Held<BigInteger> held -> ExactAnswer.held(ExactRatio.of(held.value()));
                case ExactAnswer.Unheld<BigInteger> unheld -> ExactAnswer.unheld(unheld.why());
            };
        }
        return switch (owed.dividedBy(by)
                .flatMap(quotient -> quotient.asDecimal(RoundingMode.DOWN, scale))) {
            case ExactAnswer.Held<BigDecimal> held -> ExactAnswer.held(ExactRatio.of(held.value()));
            case ExactAnswer.Unheld<BigDecimal> unheld -> ExactAnswer.unheld(unheld.why());
        };
    }

    /**
     * As much of {@code wanted} as one element may move, in the direction it is asking to move, or
     * which way the exact arithmetic could not hold the distance to the end it is moving toward.
     *
     * <p>The end an element is moving toward is the one that bounds it, and the other says nothing
     * about the move. Bounded by whichever end happened to be named, an element moving down was held
     * to how far it could go up.
     */
    private static ExactAnswer<ExactRatio> toward(ExactRatio wanted, Ends ends) {
        if (wanted.signum() >= 0) {
            if (ends.upTo() == null) {
                return ExactAnswer.held(wanted);
            }
            return switch (ends.upTo().exactly().minus(ends.from().exactly())) {
                case ExactAnswer.Unheld<ExactRatio> unheld -> unheld;
                case ExactAnswer.Held<ExactRatio> held ->
                        ExactAnswer.held(wanted.compareTo(held.value()) <= 0 ? wanted : held.value());
            };
        }
        if (ends.downTo() == null) {
            return ExactAnswer.held(wanted);
        }
        return switch (ends.downTo().exactly().minus(ends.from().exactly())) {
            case ExactAnswer.Unheld<ExactRatio> unheld -> unheld;
            case ExactAnswer.Held<ExactRatio> held ->
                    ExactAnswer.held(wanted.compareTo(held.value()) >= 0 ? wanted : held.value());
        };
    }

    /**
     * The container holding an element for each number, or nothing where one of them cannot be
     * built — with what of this compiler's building them met, which a walk keeps beside what it
     * was left ({@link WhatWasLeft#met}).
     *
     * <p>Whole elements, each composed under its own type's rules with the number written where the
     * total reads it. What the rest of an element holds is that type's question and is asked of the
     * one reader that answers it.
     *
     * <p><b>A list, and nothing else.</b> What a set holds is as many values as no two of which are
     * equal, and the elements this composes are alike wherever their numbers are — so a set of them
     * is a set of fewer, and the total it comes to is not the one it was built for. Which is work
     * for whatever first takes a total of a set: nothing does, because no operation declares a sum
     * of one and neither the walk that adds nor the walk that maps takes a set at all. Refused
     * rather than composed as a list, so that the day one arrives it arrives here.
     *
     * <p>Each element given its own values where the rules keep the elements apart beside the
     * number ({@link KeptApart#besideFor}), and the caller's where it fixed the same position: what
     * the caller asked every element to hold is asked of every element.
     */
    static Proposals filled(List<BigDecimal> split, Shape.Sequence holding, TypeView container,
                            Filling filling, KeptApart apart, Carrier elements,
                            RuleReadingContext reading) {
        if (holding.kind() != Shape.Sequence.Kind.LIST) {
            return Proposals.NONE;
        }
        return filledWith(split.stream().<Place>map(Count::of).toList(), holding, container,
                filling, apart, elements, reading);
    }

    /**
     * The same, of values on any order: each element is built around one of {@code split}, read on
     * {@code elements}. A set is written too, of values no two of which are alike: it holds each of
     * them, which is what the caller composed it for.
     */
    static Proposals filledWith(List<Place> split, Shape.Sequence holding, TypeView container,
                                Filling filling, KeptApart apart, Carrier elements,
                                RuleReadingContext reading) {
        if (holding.kind() != Shape.Sequence.Kind.LIST
                && split.stream().map(Place::canonical).distinct().count() != split.size()) {
            return Proposals.NONE;
        }
        RuleReadingSource ruleSource = reading.source();
        List<FixtureTemplate> values = new ArrayList<>();
        CompositionShortfall met = CompositionShortfall.NONE;
        for (int i = 0; i < split.size(); i++) {
            Map<TermPath, FixtureTemplate> own = apart.besideFor(i, split.size());
            if (own == null) {
                return Proposals.NONE.meeting(met.and(apart.met()));
            }
            Map<TermPath, FixtureTemplate> beside = new LinkedHashMap<>(own);
            beside.putAll(filling.beside());
            Proposals one = PlanComposer.compose(filling.plan().root(),
                    new ValuesCarryingANumber(filling.fixed(),
                            FixtureTemplate.on(elements, split.get(i),
                                    ruleSource.symbols().scope()::reach),
                            beside, filling.narrowed(), reading),
                    reading);
            met = met.and(one.met());
            if (one.isEmpty()) {
                return Proposals.NONE.meeting(met);
            }
            values.add(one.values().getFirst());
        }
        FixtureTemplate written =
                WornNames.under(container.wrappers(), FixtureTemplate.collection(values), ruleSource);
        return Proposals.ofNullable(written).meeting(met);
    }

    /**
     * One way of building an element with the number in it: the plan, and the position the number
     * is written at under it.
     *
     * <p>Both, because the second is what the first was planned against. A narrowing is written into
     * the path — {@code items[*].kind@Card.amount} — so a plan and a path from another way down are
     * a plan with nowhere to put the value.
     *
     * @param beside   the values the caller fixed inside the element, which the plan was made
     *                 against as well
     * @param narrowed the positions inside the element the caller said which case of
     */
    record Filling(ConstructionPlan plan, TermPath fixed,
                           Map<TermPath, FixtureTemplate> beside, Set<TermPath> narrowed) {}

    /**
     * What the rules keep the elements of a container a total is spread over apart at, read as
     * the two things building each element has to do about it.
     *
     * <p>A run that holds what each element is built around — the number, or the container below
     * it — keeps the elements apart by what is built there being apart, so the numbers are spread
     * with none of them alike ({@link #numbersApart}). A run beside it is a position each element
     * is given a value of its own at, decided with the number when the element is planned
     * ({@link #decided}) and handed over with it ({@link #besideFor}). Kept apart by the decoder
     * instead, every container spread out of one plan would hold its elements alike there and be
     * refused for it, which is no rule of the model's leaving nothing.
     */
    static final class KeptApart {

        /** Nothing kept apart. */
        static final KeptApart NONE =
                new KeptApart(null, List.of(), List.of(), List.of(), false, null);

        private final Type element;

        private final List<List<String>> runs;

        private final List<List<String>> beside;

        private final List<TermPath> decided;

        private final boolean numbersApart;

        private final RuleReadingContext reading;

        /** The values at each run beside, read for {@link #readFor} elements: as many as the most
         *  a container asked for so far, fewer where a run's values gave out. */
        private List<List<FixtureTemplate>> values;

        private int readFor;

        /** What of this compiler's reading those values met, which is why a run's values may
         *  give out before a container has an element for each of them. */
        private CompositionShortfall met = CompositionShortfall.NONE;

        private KeptApart(Type element, List<List<String>> runs, List<List<String>> beside,
                          List<TermPath> decided, boolean numbersApart,
                          RuleReadingContext reading) {
            this.element = element;
            this.runs = runs;
            this.beside = beside;
            this.decided = decided;
            this.numbersApart = numbersApart;
            this.reading = reading;
        }

        /**
         * Of the container read as {@code container}, held by a value whose rules keep its elements
         * apart at {@code held}, whose elements of type {@code element} stand at {@code elementAt}
         * and are each built around what stands at {@code builtAround}.
         */
        static KeptApart of(TypeView container, List<List<String>> held, Type element,
                            TermPath elementAt, TermPath builtAround, Requirements required,
                            RuleReadingContext reading) {
            List<List<String>> runs = ElementsKeptApart.at(container, held, reading);
            if (runs.isEmpty()) {
                return NONE;
            }
            boolean numbersApart = false;
            List<List<String>> beside = new ArrayList<>();
            List<TermPath> decided = new ArrayList<>();
            for (List<String> run : runs) {
                TermPath at = elementAt;
                for (String field : run) {
                    at = at.then(field);
                }
                if (builtAround.isAtOrUnder(at)) {
                    numbersApart = true;
                } else {
                    beside.add(run);
                    decided.add(underTheCasesNamed(at, required));
                }
            }
            return new KeptApart(element, runs, List.copyOf(beside), List.copyOf(decided),
                    numbersApart, reading);
        }

        /** Every run the elements are kept apart at. */
        List<List<String>> runs() {
            return runs;
        }

        /** Whether what each element is built around is to be apart from every other's. */
        boolean numbersApart() {
            return numbersApart;
        }

        /** The positions an element is given a value of its own at, spelled as the plan names
         *  them. */
        List<TermPath> decided() {
            return decided;
        }

        /**
         * What the {@code i}-th of {@code many} elements holds at each position beside, or null
         * where the values at one of them run out before it.
         */
        Map<TermPath, FixtureTemplate> besideFor(int i, int many) {
            if (beside.isEmpty()) {
                return Map.of();
            }
            // Read again only past twice what was read before: the counts are walked upward one at
            // a time, and reading at each of them would read the values of every count below it
            // again.
            if (many > readFor) {
                int upTo = Math.max(many, 2 * readFor);
                List<List<FixtureTemplate>> read = new ArrayList<>();
                CompositionShortfall reached = CompositionShortfall.NONE;
                for (List<String> run : beside) {
                    Proposals at = Witnesses.valuesApartAt(element, run, upTo, reading);
                    read.add(at.values());
                    reached = reached.and(at.met());
                }
                values = read;
                readFor = upTo;
                met = reached;
            }
            Map<TermPath, FixtureTemplate> out = new LinkedHashMap<>();
            for (int r = 0; r < beside.size(); r++) {
                List<FixtureTemplate> at = values.get(r);
                if (i >= at.size()) {
                    return null;
                }
                out.put(decided.get(r), at.get(i));
            }
            return out;
        }

        /** What of this compiler's the values {@link #besideFor} hands out met, as last read. */
        CompositionShortfall met() {
            return met;
        }
    }

    /**
     * The ways down, and what the planning gave up at.
     *
     * @param filled  one per way that planned, in the order they were reached
     * @param cutBy   the figures the planning stopped at, which are this compiler's
     */
    record Ways(List<Filling> filled, Set<CompositionBudget> cutBy,
                        List<TermPath> nothingStandsAt) {

        Ways {
            filled = List.copyOf(filled);
            cutBy = Set.copyOf(cutBy);
            nothingStandsAt = List.copyOf(nothingStandsAt);
        }

        /**
         * What this walk found, said where a reader is told nothing was composed.
         *
         * <p>One sentence per thing that happened, and never one for two of them. A way that was
         * walked and built nothing says the ways are exhausted; a position nothing stands under
         * says there was never a way to try. Told the same thing, a reader would be working out
         * which of them it was from what the sentence left out.
         */
        String said(TermPath demand) {
            if (!filled.isEmpty()) {
                return spelling(filled.stream().map(Filling::fixed).toList())
                        + (filled.size() == 1 ? " was a way down to `" : " were ways down to `")
                        + demand + "`, and none of them composed a value";
            }
            return nothingStandsAt.isEmpty()
                    ? "nothing here reaches `" + demand + "`"
                    : "nothing standing at " + spelling(nothingStandsAt)
                            + " gives a way down to `" + demand + "`";
        }

        private static String spelling(List<TermPath> paths) {
            return paths.stream().map(each -> "`" + each + "`")
                    .collect(Collectors.joining(", "));
        }
    }

    /**
     * Every way an element of {@code element} holds the number at {@code demand}.
     *
     * <p>One where the way down is a record's fields all the way, and one per case where it crosses
     * a position that holds nothing until a narrowing says what stands there. The plan is what says
     * which of those it is: a demand under such a position comes back as the position and what it
     * stands at, and this states one of them and asks again — so which cases there are, and which
     * of them a field is under, are read where a position's divisions are read and nowhere here.
     *
     * <p>Bounded by its own figure, and the figure travels so that a reader is told the rest were
     * never tried.
     *
     * <p><b>One occurrence of the number per element, and nothing here has to check it.</b> The
     * split this fills a container from is one number per element, so a way down that passed
     * through a container of its own would build a value coming to a multiple of the total. No such
     * way is asked about: a run inside one container is read at a path with none of its own on the
     * way ({@link souther.compiler.inputs.RunSource}), a total of what a location holds is read at
     * the element itself, and a run inside several containers is spread over its leaves and written
     * by {@link NestedContainersAddingUp}, which asks this for one container at a time and names
     * the container below as the position each element is asked for.
     *
     * <p>The narrowings of one position in the order the declarations write them, and a second
     * position's under whichever of the first's it was reached by. Nothing here orders the ways of
     * two positions against each other: what a caller does with them is try each, and the figure
     * above is what says how many.
     *
     * <p>Where the caller has said which case a position is, that case is the one way through it.
     * The others are ways down to an element the caller did not ask for, and stated anyway they are
     * plans the caller's narrowing refuses.
     *
     * <p>Planned with the positions each element is given a value of its own at decided as well
     * ({@link KeptApart#decided}), since a value is handed to a position the plan was made against
     * and a field the plan composes is the same for every element.
     */
    static Ways waysDown(Type element, TermPath at, TermPath demand, DemandsInside inside,
                                 KeptApart apart, RuleReadingContext reading) {
        List<Filling> found = new ArrayList<>();
        List<TermPath> nothingStandsAt = new ArrayList<>();
        // Every position spelled under the cases the caller named, which is how the plan names the
        // positions below a narrowing. Spelled without them, the number and the values would be
        // fixed at positions the plan has none of, and the element would be built around them.
        DemandsInside spelled = underTheCasesNamed(inside);
        Asking asking = new Asking(element, at, spelled, apart.decided(), reading);
        asking.add(underTheCasesNamed(demand, inside.required()));
        for (ConstructionPlan.Result answer = asking.next(); answer != null;
                answer = asking.next()) {
            TermPath fixed = asking.asked();
            switch (answer) {
                // A way whose number stands inside a container of its own holds as many occurrences
                // of it as that container's rules ask for, and the split above is one number per
                // element of the outer one. So a value built along it comes to a multiple of the
                // total it was built for, and nothing composes one until what is decomposed is the
                // occurrences rather than the elements.
                // And one element of it per choice among the values the caller asked the positions
                // inside it for: a class stands for its values through any of them, and which of
                // them a container that comes to the total can hold is what the caller finds out
                // by building it. Each choice is another way an element is built, so it is
                // counted where the ways are.
                case ConstructionPlan.Result.Planned(ConstructionPlan plan) -> {
                    boolean first = true;
                    for (Map<TermPath, FixtureTemplate> beside : eachChoice(spelled.among())) {
                        if (!first && !asking.another()) {
                            break;
                        }
                        first = false;
                        found.add(new Filling(plan, fixed, beside, narrowedAt(inside.required())));
                    }
                }
                // A narrowing to state, and the walk states each of them. Asked again rather than
                // planned around: a second narrowing may stand under the first, and which one that
                // is depends on the case this settled on.
                case ConstructionPlan.Result.Unnarrowed(TermPath where, List<Refinement> narrowings) -> {
                    // A position nothing stands under is not a way that was tried and refused.
                    // Kept as itself so that a reader is told there was never a way down rather
                    // than that the ways came to nothing.
                    if (narrowings.isEmpty()) {
                        nothingStandsAt.add(where);
                    }
                    // Never a position the caller narrowed: the plan is made against those, so
                    // what it asks to have narrowed is only what the caller left open.
                    for (Refinement narrowing : narrowings) {
                        asking.add(narrowed(fixed, where, narrowing));
                    }
                }
                case ConstructionPlan.Result.Beyond(Set<CompositionBudget> by) ->
                        asking.gaveUpAt(by);
                case ConstructionPlan.Result.Refused(ConstructionPlan.ModelRefusal why) -> {
                    switch (why) {
                        // Two narrowings at one position, which nothing here writes: every one of
                        // them was stated by this walk, one at a time, at a position the plan
                        // named and the caller left open, and what the caller asked was settled
                        // to hold together before the walk began.
                        case ConstructionPlan.ModelRefusal.Conflict conflict ->
                                throw new IllegalStateException("`" + conflict.at() + "` would have"
                                        + " to be both " + conflict.one().spelled() + " and "
                                        + conflict.other().spelled()
                                        + ", though one narrowing was stated");
                        // A collection on the way down holds nothing, so nothing stands inside it
                        // and there was never a way to try. Which is what the list beside this one
                        // already says: a position nothing stands under is a position nothing
                        // stands under whether the declarations put nothing there or the rules
                        // leave no room for it, and a walk that never had a way is the same news
                        // either way.
                        case ConstructionPlan.ModelRefusal.NoRoom noRoom ->
                                nothingStandsAt.add(noRoom.at());
                    }
                }
            }
        }
        return new Ways(found, asking.stoppedBy(), nothingStandsAt);
    }

    /**
     * The ways this walk has left to ask the plan about, and the figure that says how many it may.
     *
     * <p><b>The asking and the counting are one thing.</b> What multiplies here is the cases of
     * every position that has to be narrowed, and what bounds the walk is therefore how many times
     * it asks — not how many answers it keeps, which is nothing at all where no branch plans. Held
     * apart, the figure was written against whichever count was nearest the top of the loop, and a
     * walk that kept none of what it asked about ran through the whole cross product saying nothing
     * had stopped it.
     *
     * <p>So a caller cannot ask without being counted: there is one way in, and a second place that
     * reached the plan another way would be a second walk rather than an unbounded one.
     */
    private static final class Asking {

        private final Type element;
        private final TermPath at;
        private final DemandsInside inside;
        private final List<TermPath> apart;
        private final RuleReadingContext reading;
        private final Deque<TermPath> left = new ArrayDeque<>();
        private final Set<CompositionBudget> stoppedBy =
                EnumSet.noneOf(CompositionBudget.class);
        private TermPath asked;
        private int asks;

        Asking(Type element, TermPath at, DemandsInside inside, List<TermPath> apart,
               RuleReadingContext reading) {
            this.element = element;
            this.at = at;
            this.inside = inside;
            this.apart = apart;
            this.reading = reading;
        }

        /** One more way to ask about, which is what stating a narrowing leaves. */
        void add(TermPath way) {
            left.addLast(way);
        }

        /**
         * What the plan says about the next way, or null where there is no next one to ask about.
         *
         * <p>Null for two reasons and the figures tell them apart: nothing is left to ask, or this
         * has asked as often as it may — which {@link #stoppedBy()} says and a reader is owed.
         */
        ConstructionPlan.Result next() {
            if (left.isEmpty()) {
                return null;
            }
            // Read here and handed on, so that one place decides both that this asks no more and
            // which figure it stopped at. Named again where the answer is made, the two could part.
            CompositionBudget tried = CompositionBudget.WAYS_DOWN_TO_A_TOTAL_TRIED;
            if (asks == tried.maximum()) {
                stoppedBy.add(tried);
                return null;
            }
            asks++;
            asked = left.removeFirst();
            // The number's position and every position the caller asked for, decided together, and
            // the caller's narrowings with them: one element asked for all of it at once.
            Set<TermPath> decided = new LinkedHashSet<>();
            decided.add(asked);
            decided.addAll(inside.among().keySet());
            decided.addAll(apart);
            return ConstructionPlan.of(element, at, reading.source().inners(),
                    reading.source().symbols(),
                    reading.source().kinds(), reading.source().sums(), decided,
                    inside.required(), ConstructionPlan.ContentsComposed.NONE,
                    (_, building) -> ConstructionPlan.ItMayHold.counting(
                            Partitions.heldRange(building, reading, null)));
        }

        /** The way the last answer is about. */
        TermPath asked() {
            return asked;
        }

        /**
         * One more way an element is built along the last answer, where the figure leaves room for
         * it; false, with the figure said, where it does not.
         */
        boolean another() {
            CompositionBudget tried = CompositionBudget.WAYS_DOWN_TO_A_TOTAL_TRIED;
            if (asks == tried.maximum()) {
                stoppedBy.add(tried);
                return false;
            }
            asks++;
            return true;
        }

        /** What the planning of one way gave up at, which is this compiler's as the figure here is. */
        void gaveUpAt(Set<CompositionBudget> by) {
            stoppedBy.addAll(by);
        }

        /** Every figure reached, whether by the planning or by this walk. */
        Set<CompositionBudget> stoppedBy() {
            return stoppedBy;
        }
    }

    /** {@code inside} with every position it asks for spelled under the cases it names. */
    private static DemandsInside underTheCasesNamed(DemandsInside inside) {
        if (inside.required().refinements().isEmpty()) {
            return inside;
        }
        Map<TermPath, List<FixtureTemplate>> among = new LinkedHashMap<>();
        inside.among().forEach((path, values) ->
                among.put(underTheCasesNamed(path, inside.required()), values));
        return new DemandsInside(among, inside.required());
    }

    /**
     * One value apiece for the positions of {@code among}, every way there is to choose them: the
     * first value of each first, and the first position the slowest to move, so the choice nearest
     * what was asked comes first and two runs of one model choose in one order.
     */
    private static Iterable<Map<TermPath, FixtureTemplate>> eachChoice(
            Map<TermPath, List<FixtureTemplate>> among) {
        List<TermPath> positions = List.copyOf(among.keySet());
        return () -> new Iterator<>() {

            private final int[] at = new int[positions.size()];

            private boolean done;

            @Override
            public boolean hasNext() {
                return !done;
            }

            @Override
            public Map<TermPath, FixtureTemplate> next() {
                if (done) {
                    throw new NoSuchElementException();
                }
                Map<TermPath, FixtureTemplate> chosen = new LinkedHashMap<>();
                for (int i = 0; i < positions.size(); i++) {
                    chosen.put(positions.get(i), among.get(positions.get(i)).get(at[i]));
                }
                // Moved on from the last position back, which is what leaves the first the slowest.
                int i = positions.size() - 1;
                while (i >= 0 && ++at[i] == among.get(positions.get(i)).size()) {
                    at[i] = 0;
                    i--;
                }
                done = i < 0;
                return chosen;
            }
        };
    }

    /**
     * Each position {@code required} names a case at, spelled the way the plan names it: under the
     * case it is narrowed to, and under the cases of the positions above it.
     *
     * <p>The plan's spelling and no other. A position said without its case is a different path from
     * the one the plan holds, and a reader matching the two by stripping the case would take a
     * position narrowed to one case for the same position narrowed to another.
     */
    private static Set<TermPath> narrowedAt(Requirements required) {
        Set<TermPath> out = new LinkedHashSet<>();
        for (TermPath each : required.refinements().keySet()) {
            out.add(underTheCasesNamed(each, required));
        }
        return out;
    }

    /**
     * {@code path} with the case {@code required} names written in after every position it names
     * one at, where the path does not already go on under a case there.
     */
    static TermPath underTheCasesNamed(TermPath path, Requirements required) {
        TermPath out = TermPath.of(path.head());
        List<TermPath.Step> steps = path.steps();
        for (int i = 0; i <= steps.size(); i++) {
            // A case named, and not several: a position left several cases is no position the
            // plan builds, so the path goes on under the sum, where the plan says no case was
            // stated.
            CasesLeft named = required.at(out);
            boolean refinedNext = i < steps.size()
                    && steps.get(i) instanceof TermPath.Step.Refine;
            if (named != null && named.only() != null && !refinedNext) {
                out = out.refine(named);
            }
            if (i == steps.size()) {
                break;
            }
            out = switch (steps.get(i)) {
                case TermPath.Step.Field(String name) -> out.then(name);
                case TermPath.Step.Element _ -> out.element();
                case TermPath.Step.Key _ -> out.key();
                case TermPath.Step.Refine(CasesLeft already) -> out.refine(already);
            };
        }
        return out;
    }

    /**
     * {@code demand} with {@code narrowing} written in at {@code where}.
     *
     * <p>Written into the path rather than carried beside it, because a path states the
     * requirements for the position it names to exist ({@link TermPath#requirements}) and the plan
     * names every position below a narrowing under the narrowed spelling. Kept beside it, the value
     * would be fixed at a position the plan has none of.
     */
    private static TermPath narrowed(TermPath demand, TermPath where, Refinement narrowing) {
        TermPath out = where.refine(narrowing);
        for (TermPath.Step step
                : demand.steps().subList(where.steps().size(), demand.steps().size())) {
            out = switch (step) {
                case TermPath.Step.Field(String name) -> out.then(name);
                case TermPath.Step.Element _ -> out.element();
                case TermPath.Step.Key _ -> out.key();
                case TermPath.Step.Refine(CasesLeft already) -> out.refine(already);
            };
        }
        return out;
    }

    /**
     * Where an element starts, how far it may be moved either way, and what it has to be inside.
     *
     * <p>The first three are how a decomposition is arrived at and the last is what it is held to.
     * A range open at an end names no value there, and a dense one names none beside a value it
     * excludes — so what an element starts at is a value the carrier picks out of the range rather
     * than an end read off it, and how far it may be moved is nothing at all where the end it is
     * moving toward cannot be named. None of that makes a decomposition wrong on its own, which is
     * why the range travels with them and every number that comes out is put back to it.
     *
     * <p>Both ends and not the top alone. An element moves down as readily as up, and an element
     * held to the distance to the top while moving down is one that walks out of the range and is
     * caught by it — which is a decomposition lost for a reason about this reader.
     *
     * <p>Held as the counts the carrier and the rules name, not as exact ratios. A count is the
     * number and the places it was written to, and a level share is rounded to the places the
     * numbers taking part in it were written to — a start written {@code 0.00} shares a total out
     * to two places where one written {@code 0} would not. An exact ratio holds only the number,
     * so once an end has become one there is nothing left to ask for its places. Every sum and
     * difference of the ends is still worked out exactly, through {@link Count#exactly}, which
     * loses nothing.
     *
     * @param downTo null where nothing floors an element, or where the floor is a value the order
     *               has no value beside
     * @param upTo   the same at the other end
     */
    record Ends(Count from, Count downTo, Count upTo, NumericDomain.Bounds runs) {

        /**
         * Whether {@code many} elements standing on these ends can come to {@code total} at all.
         *
         * <p>Arithmetic on the ends and nothing else. Every element starts at {@link #from} and may
         * be moved as far as the end it is moving toward, so the furthest {@code many} of them
         * reach together is that distance taken {@code many} times — and a total past it is one no
         * arrangement of that many comes to, whatever the arrangement.
         *
         * <p>True where the end it would be moving toward names no value, since an order open that
         * way puts nothing in the way of reaching any total. And true wherever the sums allow it
         * without asking whether the values between are the carrier's: what this is asked for is
         * whether there is nothing to reach, so admitting a total the carrier turns out to refuse
         * costs a claim of completeness nobody had to make, and denying one it admits would be a
         * claim of completeness nothing showed.
         *
         * <p>True as well where the exact arithmetic could not hold a distance this needed: the
         * claim this makes when it answers false is that nothing further is worth trying, and that
         * is the one direction an unheld difference must never be read as.
         */
        boolean reaches(BigDecimal total, int many) {
            ExactRatio manyTimes = ExactRatio.of(many);
            if (!(from.exactly().times(manyTimes).flatMap(counted -> ExactRatio.of(total).minus(counted))
                    instanceof ExactAnswer.Held<ExactRatio> heldOwed)) {
                return true;
            }
            ExactRatio owed = heldOwed.value();
            if (owed.isZero()) {
                return true;
            }
            Count end = owed.signum() > 0 ? upTo : downTo;
            if (end == null) {
                return true;
            }
            // True as well where the exact arithmetic could not hold this distance, for the same
            // reason as every other one above: false is the claim that nothing further is worth
            // trying, and an unheld distance never establishes that.
            return switch (end.exactly().minus(from.exactly())) {
                case ExactAnswer.Unheld<ExactRatio> _ -> true;
                case ExactAnswer.Held<ExactRatio> distance ->
                        switch (distance.value().abs().times(manyTimes)) {
                            case ExactAnswer.Unheld<ExactRatio> _ -> true;
                            case ExactAnswer.Held<ExactRatio> furthest ->
                                    owed.abs().compareTo(furthest.value()) <= 0;
                        };
            };
        }

        static Ends of(NumericDomain.Bounds runs, Carrier elements) {
            // A value of the carrier that the rules leave, which is the one reader of that question.
            // Read as "the least the range names", a range open below had no start and a dense one
            // held away from a value had the wrong one.
            if (!(elements.somethingInside(runs.min(), runs.max()) instanceof Count from)) {
                return null;
            }
            return new Ends(from, inward(runs.min(), elements, true),
                    inward(runs.max(), elements, false), runs);
        }

        /**
         * The value of an end that is inside it, or null where the order names none.
         *
         * <p>An end written exclusively is a value taken out of the range, and the value beside it
         * is the carrier's to name — asked of {@link BoundaryDomain}, which is where that question
         * has its answer and where a carrier with no smallest step says it has none.
         */
        private static Count inward(Endpoint end, Carrier elements, boolean upward) {
            if (end == null || !(end.at() instanceof Count at)) {
                return null;
            }
            if (end.inclusive()) {
                return at;
            }
            BoundaryDomain beside = BoundaryDomain.on(elements);
            Optional<Place> next =
                    upward ? beside.successor(at) : beside.predecessor(at);
            return next.orElse(null) instanceof Count on ? on : null;
        }
    }

    private static TermRealizations.Realization none(
            Generator.UnresolvedCombination.Reason why) {
        return new TermRealizations.Realization.None(why);
    }

    private ContainersAddingUp() {}
}
