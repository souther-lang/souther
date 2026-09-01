package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.check.DeclaredBounds;
import souther.compiler.check.ReadingPolicy;
import souther.compiler.check.Shape;
import souther.compiler.check.NumericMeasures;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeView;
import souther.compiler.inputs.BoundaryDomain;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.CountDomain;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.List;

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

    /** What this stops at, named where every budget of this compiler's is named. */
    private static final int MOST_ELEMENTS_A_ROW_CARRIES =
            CompositionBudget.ELEMENTS_A_TOTAL_IS_SPREAD_OVER.maximum();

    private static final int HOW_MANY_SHAPES_ARE_OFFERED =
            CompositionBudget.SHAPES_OF_A_TOTAL_OFFERED.maximum();

    /**
     * How many ways a difference is spread over the elements, which is how many this walk has.
     *
     * <p>Read off {@link Spread} rather than written down beside it. A third way of spreading is a
     * budget raised, and a figure of its own here would be a second declaration that stayed at two.
     */
    static int decompositionsOffered() {
        return Spread.values().length;
    }

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
                                           Symbols symbols, ReadingPolicy policy) {
        // Which number is being built for, read off the answer that says which number it is of.
        // Named beside it, the two were free to be about two numbers and this would fill a
        // container found under one path with elements counted on another's order.
        RealizationTarget target = RealizationTarget.of(orders.term());
        Carrier elements = orders.answered();
        if (!(answer instanceof Count total) || elements == null) {
            return none(Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
        }
        if (!(TypeView.of(container, symbols).shape() instanceof Shape.Sequence holding)) {
            // A total is taken of a container, and what is declared at the root is not one. Which is
            // a term nobody should have been able to build; said here rather than by composing a
            // value of whatever shape is there.
            return none(Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
        }
        DeclaredBounds.CountRange howMany = howMany(container, target.writeRoot(), within, symbols);
        NumericDomain.Bounds runs =
                within.runsBetween(new NumericTerm.ValueOf(occurrences(target)));
        Ends ends = Ends.of(runs == null ? NumericDomain.Bounds.OPEN : runs, elements);
        if (ends == null) {
            // Nowhere for an element to stand. Which is the rules leaving the elements nothing, and
            // is said as a container this composed none of rather than as a total nothing reaches.
            return none(Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
        }
        List<TermPath.Step> under = stepsInsideAnElement(target);
        List<FixtureTemplate> built = new ArrayList<>();
        int cap = Math.min(howMany.most(), MOST_ELEMENTS_A_ROW_CARRIES);
        // What this walk did not do, recorded as it decides not to do it, and as which budget of
        // this compiler's decided it. Held as one flag, the three ways of leaving something unmade
        // were one fact and a reader was told a search stopped without being told what would let it
        // go further — and worked out afterwards from the ends, they cannot all be seen at once.
        java.util.Set<CompositionBudget> left = java.util.EnumSet.noneOf(CompositionBudget.class);
        if (cap < howMany.most()) {
            left.add(CompositionBudget.ELEMENTS_A_TOTAL_IS_SPREAD_OVER);
        }
        // Asked where a container is added and nowhere else. What the budget counts is containers,
        // and a walk that asked at the top of the counts was asking about containers in a place that
        // steps by counts — so a count offering two of them stepped past the figure by one, and how
        // many were offered was the inner walk's grain rather than what is written down here.
        offering:
        for (int many = Math.max(howMany.least(), 0); many <= cap; many++) {
            // More than one element is more than one decomposition, whether or not this made a
            // second: what is offered is two shapes of the many, and the many are what a rule taking
            // a value out of the middle of a run tells apart.
            if (many > 1) {
                left.add(CompositionBudget.DECOMPOSITIONS_OF_A_TOTAL_OFFERED);
            }
            for (Spread how : Spread.values()) {
                List<BigDecimal> split = splitting(total.at(), many, ends, how, elements);
                FixtureTemplate one = split == null ? null
                        : filled(split, holding, container, under, elements, symbols, policy);
                if (one == null || built.contains(one)) {
                    continue;
                }
                if (built.size() == HOW_MANY_SHAPES_ARE_OFFERED) {
                    left.add(CompositionBudget.SHAPES_OF_A_TOTAL_OFFERED);
                    break offering;
                }
                built.add(one);
            }
        }
        if (!built.isEmpty()) {
            return new TermRealizations.Realization.Built(built, left);
        }
        // Nothing was composed, so what the budgets stopped is the composing itself and not the rest
        // of an offer. Where none of them ran out, this is a total nothing here writes a container
        // for, which is a different thing to tell anybody.
        return left.isEmpty()
                ? none(Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE)
                : new TermRealizations.Realization.Stopped(left);
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
    private static DeclaredBounds.CountRange howMany(Type container, TermPath root,
                                                     SearchRegion within, Symbols symbols) {
        DeclaredBounds.CountRange declared =
                DeclaredBounds.countsHeld(container, symbols, null);
        ValueName.Stdlib counts = NumericMeasures.takenOf(container, symbols);
        NumericTerm.FromOnePosition term = counts == null ? null
                : NumericTerm.TakenOf.of(counts, root, container, symbols);
        NumericDomain.Bounds runs = term == null ? null : within.runsBetween(term);
        if (runs == null) {
            return declared;
        }
        int least = Math.max(declared.least(), CountDomain.leastFrom(runs.min()));
        int most = Math.min(declared.most(), CountDomain.mostFrom(runs.max()));
        return new DeclaredBounds.CountRange(least, most);
    }

    /**
     * The path whose occurrences inside the root are added up.
     *
     * <p>The element itself where the total is of what a location holds, and the run's own path
     * where it is over a run. One question about two terms and not two questions: what is added up
     * is what stands at a path under the container, and where the path stops is the whole
     * difference.
     */
    private static TermPath occurrences(RealizationTarget target) {
        return switch (target) {
            case RealizationTarget.AtOnePosition one -> one.term().position().element();
            case RealizationTarget.OverARun over -> over.term().source().subjectPath();
        };
    }

    /**
     * The way down from one element to the number, which is the occurrences' path with the container
     * and the step into it taken off.
     *
     * <p>Steps and not a path. What is named is a way down from a value whose own location the
     * element composer does not know, and a {@link TermPath} is rooted at a parameter — so a
     * relative path written as one would be a second spelling of a location.
     */
    private static List<TermPath.Step> stepsInsideAnElement(RealizationTarget target) {
        List<TermPath.Step> steps = occurrences(target).steps();
        return List.copyOf(steps.subList(target.writeRoot().steps().size() + 1, steps.size()));
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
    private enum Spread {

        /** The whole difference on as few elements as will carry it, the rest where they started. */
        MASSED,

        /** As near an equal share each as the order allows, the last taking what division left. */
        LEVEL
    }

    /**
     * The numbers {@code many} elements hold for the container to come to {@code total}, or null
     * where this shape reaches none.
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
    private static List<BigDecimal> splitting(BigDecimal total, int many, Ends ends, Spread how,
                                              Carrier elements) {
        if (many == 0) {
            return total.signum() == 0 ? List.of() : null;
        }
        BigDecimal owed = total.subtract(ends.from().multiply(BigDecimal.valueOf(many)));
        List<BigDecimal> split = new ArrayList<>();
        for (int i = 0; i < many; i++) {
            BigDecimal wanted = how == Spread.MASSED ? owed : shared(owed, many - i, elements);
            BigDecimal add = toward(wanted, ends, elements);
            BigDecimal at = ends.from().add(add);
            // Put back to the rules and to the carrier, which are the two things a number has to be
            // to be a value here. Where an element starts and how far it may be moved are worked out
            // from the ends and are this reader's arithmetic; whether what came of them is a value
            // is not, and a decomposition that reads its own workings back would be sound only for
            // as long as the workings are.
            if (!ends.runs().admits(Count.of(at))
                    || !(elements.onTheGrid(Count.of(at)) instanceof Count on)
                    || on.at().compareTo(at) != 0) {
                return null;
            }
            split.add(at);
            owed = owed.subtract(add);
        }
        return owed.signum() == 0 ? List.copyOf(split) : null;
    }

    /**
     * One element's share of what is still owed, over the elements still to be given one.
     *
     * <p>Toward nought, so the elements before the last take no more than their share and the last
     * takes what division left over. Which is what makes the shares add up without a remainder to
     * place: the last element is given whatever is still owed, whatever the division came to.
     *
     * <p>An order that steps divides to a whole number of its counts; one that does not is divided
     * as far as the numbers being added were written, since a share finer than that is a value the
     * total was never stated to a.
     */
    private static BigDecimal shared(BigDecimal owed, int among, Carrier elements) {
        BigDecimal by = BigDecimal.valueOf(among);
        return elements.spacing() == Granularity.DISCRETE
                ? owed.divideToIntegralValue(by)
                : owed.divide(by, Math.max(owed.scale(), 1), java.math.RoundingMode.DOWN);
    }

    /**
     * As much of {@code wanted} as one element may move, in the direction it is asking to move.
     *
     * <p>The end an element is moving toward is the one that bounds it, and the other says nothing
     * about the move. Bounded by whichever end happened to be named, an element moving down was held
     * to how far it could go up.
     */
    private static BigDecimal toward(BigDecimal wanted, Ends ends, Carrier elements) {
        if (wanted.signum() >= 0) {
            return ends.upTo() == null ? wanted
                    : wanted.min(ends.upTo().subtract(ends.from()));
        }
        return ends.downTo() == null ? wanted
                : wanted.max(ends.downTo().subtract(ends.from()));
    }

    /**
     * The container holding an element for each number, or null where one of them cannot be built.
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
     */
    private static FixtureTemplate filled(List<BigDecimal> split, Shape.Sequence holding,
                                          Type container, List<TermPath.Step> under,
                                          Carrier elements, Symbols symbols, ReadingPolicy policy) {
        if (holding.kind() != Shape.Sequence.Kind.LIST) {
            return null;
        }
        List<FixtureTemplate> values = new ArrayList<>();
        for (BigDecimal each : split) {
            FixtureTemplate one = Partitions.carrying(holding.element(), under,
                    FixtureTemplate.on(elements, Count.of(each), symbols.scope()::reach),
                    symbols, policy);
            if (one == null) {
                return null;
            }
            values.add(one);
        }
        return Witnesses.wrapped(container, FixtureTemplate.collection(values), symbols);
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
     * @param downTo null where nothing floors an element, or where the floor is a value the order
     *               has no value beside
     * @param upTo   the same at the other end
     */
    private record Ends(BigDecimal from, BigDecimal downTo, BigDecimal upTo,
                        NumericDomain.Bounds runs) {

        static Ends of(NumericDomain.Bounds runs, Carrier elements) {
            // A value of the carrier that the rules leave, which is the one reader of that question.
            // Read as "the least the range names", a range open below had no start and a dense one
            // held away from a value had the wrong one.
            if (!(elements.somethingInside(runs.min(), runs.max()) instanceof Count from)) {
                return null;
            }
            return new Ends(from.at(), inward(runs.min(), elements, true),
                    inward(runs.max(), elements, false), runs);
        }

        /**
         * The value of an end that is inside it, or null where the order names none.
         *
         * <p>An end written exclusively is a value taken out of the range, and the value beside it
         * is the carrier's to name — asked of {@link BoundaryDomain}, which is where that question
         * has its answer and where a carrier with no smallest step says it has none.
         */
        private static BigDecimal inward(Endpoint end, Carrier elements, boolean upward) {
            if (end == null || !(end.at() instanceof Count at)) {
                return null;
            }
            if (end.inclusive()) {
                return at.at();
            }
            BoundaryDomain beside = BoundaryDomain.on(elements);
            java.util.Optional<Place> next =
                    upward ? beside.successor(at) : beside.predecessor(at);
            return next.orElse(null) instanceof Count on ? on.at() : null;
        }
    }

    private static TermRealizations.Realization none(
            Generator.UnresolvedCombination.Reason why) {
        return new TermRealizations.Realization.None(why);
    }

    private ContainersAddingUp() {}
}
