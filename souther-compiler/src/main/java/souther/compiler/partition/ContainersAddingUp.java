package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.check.DeclaredBounds;
import souther.compiler.check.ReadingPolicy;
import souther.compiler.check.Shape;
import souther.compiler.check.NumericMeasures;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeView;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.CountDomain;
import souther.compiler.numeric.Endpoint;
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
 * hold is what the declarations say ({@link DeclaredBounds#countsHeld}); what one occurrence may be
 * is what the region leaves the number at that path. A container built without asking either is one
 * the decoder refuses, and the point it was built for then reads as an edge every value was refused
 * at rather than as one this did not fill.
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
     * How many elements a container this composes is worth carrying.
     *
     * <p>Its own figure and not {@link Witnesses}'s, though they agree: what bounds a container
     * built to hold a count is how many a row is worth reading, and what bounds one built to reach a
     * total is the same thing said of the same reader. Held as one constant, a change made for one
     * of them would move the other for no reason anybody could state.
     */
    private static final int MOST_ELEMENTS_A_ROW_CARRIES = 64;

    /**
     * How many containers are offered for one total.
     *
     * <p>More than one, because the counts that reach a total are not alike to the rules the
     * elements are under: a container of ten is refused by a rule about how many it holds while one
     * of eleven is not, and the search that puts them through the decoder has nothing else to try.
     * Small, because they are alike to the total, and a reader offered a third is being offered the
     * same row again.
     */
    private static final int HOW_MANY_SHAPES_ARE_OFFERED = 2;

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
    static TermRealizations.Realization to(Place answer, RealizationTarget target, Type container,
                                           TermOrders orders, SearchRegion within,
                                           Symbols symbols, ReadingPolicy policy) {
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
        NumericDomain.Bounds each = within.runsBetween(new NumericTerm.ValueOf(occurrences(target)));
        Ends ends = Ends.of(each == null ? NumericDomain.Bounds.OPEN : each, elements);
        if (ends == null) {
            // An end the carrier cannot name the first value past, which is what an exclusive end on
            // an order without a smallest step is. Nothing to decompose against.
            return none(Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
        }
        List<TermPath.Step> under = stepsInsideAnElement(target);
        List<FixtureTemplate> built = new ArrayList<>();
        int cap = Math.min(howMany.most(), MOST_ELEMENTS_A_ROW_CARRIES);
        for (int many = Math.max(howMany.least(), 0);
                many <= cap && built.size() < HOW_MANY_SHAPES_ARE_OFFERED; many++) {
            List<BigDecimal> split = splitting(total.at(), many, ends, elements);
            FixtureTemplate one = split == null ? null
                    : filled(split, holding, container, under, elements, symbols, policy);
            if (one != null) {
                built.add(one);
            }
        }
        if (!built.isEmpty()) {
            return new TermRealizations.Realization.Built(built,
                    cap < howMany.most() && built.size() < HOW_MANY_SHAPES_ARE_OFFERED
                            ? Generator.UnresolvedCombination.Reason.SEARCH_LIMIT : null);
        }
        // Every count the rules allow was tried, up to the one this stops at. Where the rules allow
        // more than that, the counts past it were never tried and saying "nothing composes one"
        // would be this compiler's budget reported as the model's answer.
        return none(cap < howMany.most() ? Generator.UnresolvedCombination.Reason.SEARCH_LIMIT
                : Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
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
        return least > most ? DeclaredBounds.CountRange.NONE
                : new DeclaredBounds.CountRange(least, most);
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
     * The numbers {@code many} elements hold for the container to come to {@code total}, or null
     * where none do.
     *
     * <p>Every element at the least it may be, and the difference poured into them in turn up to the
     * most each may be. Which is a choice among the decompositions and not the only one: what is
     * owed is a container that reads back as the total, and the elements' own rules answer the rest.
     *
     * <p>Null for three unlike reasons and one answer: too many elements to hold so little, too few
     * to hold so much, and a difference the carrier's values cannot be moved by. The third is why
     * what is poured is put back on the carrier and the remainder is checked at the end — a walk
     * that trusted the ends would hand over values no order has.
     */
    private static List<BigDecimal> splitting(BigDecimal total, int many, Ends ends,
                                              Carrier elements) {
        if (many == 0) {
            return total.signum() == 0 ? List.of() : null;
        }
        BigDecimal owed = total.subtract(ends.low().multiply(BigDecimal.valueOf(many)));
        if (owed.signum() < 0) {
            return null;
        }
        List<BigDecimal> split = new ArrayList<>();
        for (int i = 0; i < many; i++) {
            BigDecimal add = ends.high() == null ? owed
                    : owed.min(ends.high().subtract(ends.low()));
            BigDecimal at = ends.low().add(add);
            // On the carrier, because the ends of a range say where its values run and not which
            // numbers between them are values. A total reached by a decomposition the order does not
            // hold is a total this count does not reach.
            if (!(elements.onTheGrid(Count.of(at)) instanceof Count on)
                    || on.at().compareTo(at) != 0) {
                return null;
            }
            split.add(at);
            owed = owed.subtract(add);
        }
        return owed.signum() == 0 ? List.copyOf(split) : null;
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
     * The numbers a range runs between, as values the carrier holds.
     *
     * <p>The low end is where every element starts and the high end is how far one may be moved, so
     * both are needed as numbers rather than as ends. A range open below starts at nought — the
     * number a walk that adds starts from, and the one an element contributing nothing holds.
     *
     * @param high null where nothing caps an element, which is not a number and is not nought either
     */
    private record Ends(BigDecimal low, BigDecimal high) {

        static Ends of(NumericDomain.Bounds runs, Carrier elements) {
            BigDecimal low = inward(runs.min(), elements, true);
            BigDecimal high = inward(runs.max(), elements, false);
            if (runs.min() != null && low == null || runs.max() != null && high == null) {
                return null;
            }
            return new Ends(low == null ? BigDecimal.ZERO : low, high);
        }

        /**
         * The first value inside an end, or null where the carrier names none.
         *
         * <p>An end written exclusively is a value taken out of the range, and the first one inside
         * it is a step along the carrier — which exists only where the carrier's values count.
         * Nothing here moves a dense end inward: between two decimals there is no next value, and a
         * number chosen as though there were would be outside the rules.
         */
        private static BigDecimal inward(Endpoint end, Carrier elements, boolean upward) {
            if (end == null || !(end.at() instanceof Count at)) {
                return null;
            }
            if (end.inclusive()) {
                return at.at();
            }
            if (!elements.counts()) {
                return null;
            }
            BigDecimal step = BigDecimal.ONE;
            return upward ? at.at().add(step) : at.at().subtract(step);
        }
    }

    private static TermRealizations.Realization none(
            Generator.UnresolvedCombination.Reason why) {
        return new TermRealizations.Realization.BuiltNone(why);
    }

    private ContainersAddingUp() {}
}
