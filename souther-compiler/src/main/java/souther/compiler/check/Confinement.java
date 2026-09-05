package souther.compiler.check;

import souther.compiler.numeric.OrderedIntervals;
import souther.compiler.regex.Meter;
import souther.compiler.regex.PatternPlan;
import souther.compiler.values.Allowance;
import souther.compiler.values.ConjoinedAdmissibleValues;
import souther.compiler.values.Emptiness;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.Function;

/**
 * Which values the positions of one value may take, said in both of the languages that say it.
 *
 * <p>Two readings and one answer. Which values a position may hold is a set, and where its order
 * stops is a range, and neither has a word for what the other holds — a pattern names no ends and
 * an ordering names no finite set. So a clause reaches whichever of them has a word for it, and
 * whether anything satisfies the rules is a question about the two of them together.
 *
 * <p><b>Which is why they are held here and not side by side.</b> Asked of each of them in turn, the
 * answer is that something exists whenever the reading that happened to be asked had nothing to say:
 * {@code String.startsWith("JP", value) && value < "JA"} is a set and a range with no string in
 * both, and each reading, asked alone, finds nothing wrong. That sentence was written in five places
 * and its reason — that either language can hold the whole answer on its own — in every one of them.
 * A type that holds the pair is what makes it unwritable rather than forbidden.
 *
 * <p>The rule is one method and the readings differ only in what they can say. A reading whose
 * values are still descriptions has not worked out what they come to and says so; one whose values
 * are sets asks the order about every alternative it holds.
 *
 * <p><b>Not everything two readings could show together.</b> What is proven here is what the
 * reductions written here prove, and {@link Emptiness#UNDECIDED} is what stands where none of them
 * did — a state nothing showed empty is not one shown to have a value. The other domains of
 * {@link ConstraintState} are outside this and stay outside it: a reduction between the numbers and
 * an order is another one of these, added the same way, and calling this the whole of a
 * conjunction's satisfiability would be a claim the reductions in it do not carry.
 *
 * @param <A> what a position is called
 */
sealed interface Confinement<A> permits Confinement.OfAConjunction, ReadByClauses, Settlement,
        StatedByClauses.Said, StatedTogether.Said {

    /** Where each position's order stops, over the rules taken in. */
    OrderedIntervals<A> ordered();

    /**
     * What the values leave, every alternative asked against where its positions stop.
     *
     * <p>What each reading of the values can say, and no more: a reduction needs the sets
     * themselves, so a reading holding descriptions of them answers what it can settle without
     * building and leaves the rest open.
     */
    Emptiness ofTheValues();

    /**
     * Whether anything satisfies both readings.
     *
     * <p>The one place the two are put together, and the whole of the rule. An order that holds no
     * value at some position leaves the value none whatever the sets admit; otherwise the answer is
     * the values', which is where the sets and the ranges meet.
     */
    default Emptiness admits() {
        return ordered().isBottom() ? Emptiness.EMPTY : ofTheValues();
    }

    /** Whether it is settled that nothing satisfies them. */
    default boolean holdsNothing() {
        return admits() == Emptiness.EMPTY;
    }

    /**
     * The same question, answered out of what something has already built.
     *
     * <p>For a caller deciding whether to keep a branch while a reading is still being put together.
     * What it may spend is the answer's own allowance, and spending it to drop a branch would make
     * what a declaration costs depend on how its author bracketed it — so what is asked is what is
     * established, and a branch nothing established is kept.
     */
    default Emptiness alreadyEstablished(Allowance<A> by) {
        return ordered().isBottom() ? Emptiness.EMPTY : ofTheValuesAlreadyBuilt(by);
    }

    /** What the values leave, out of the machines something has already built. */
    Emptiness ofTheValuesAlreadyBuilt(Allowance<A> by);

    /**
     * The readings of several declarations' clauses, conjoined, beside where their orders stop.
     *
     * <p>The one of these whose values are worked out, so the one that reduces. What each position
     * is ordered on is carried rather than looked up: the carrier was settled where the clauses were
     * read, and a second table worked out here would be a second answer to a question the reading
     * already asked.
     */
    final class OfAConjunction<A> implements Confinement<A> {

        private final ConjoinedAdmissibleValues<A> values;
        private final OrderedIntervals<A> ordered;
        private final Map<A, Carrier> carriers;

        OfAConjunction(ConjoinedAdmissibleValues<A> values, OrderedIntervals<A> ordered,
                       Map<A, Carrier> carriers) {
            this.values = values;
            this.ordered = ordered;
            this.carriers = Collections.unmodifiableMap(new LinkedHashMap<>(carriers));
        }

        /** Nothing read, so nothing ruled out. */
        static <A> OfAConjunction<A> top() {
            return new OfAConjunction<>(ConjoinedAdmissibleValues.top(), OrderedIntervals.top(),
                    Map.of());
        }

        ConjoinedAdmissibleValues<A> values() {
            return values;
        }

        Map<A, Carrier> carriers() {
            return carriers;
        }

        @Override
        public OrderedIntervals<A> ordered() {
            return ordered;
        }

        /**
         * Every alternative asked, at every position it names, whether the values it admits reach
         * inside the range the order leaves.
         *
         * <p>Per alternative, which is what the reading's own walk is for. What a position may hold
         * across the alternatives is their union, and a range met against that is met against a
         * value no alternative stands for.
         *
         * <p>A position on no order is one nothing here can refuse. What it admits is a set and
         * there is no range to share a value with, so the alternative stands as far as this asks.
         */
        @Override
        public Emptiness ofTheValues() {
            // A meter of this question's own, spent on this asking of it. What may be built to
            // decide whether a declaration has a value cannot come out of the position's own
            // allowance: the same rules would then be decided differently depending on what the
            // readings before them had already built.
            Meter meter = PatternPlan.Budget.OF_WHAT_A_SET_AND_A_RANGE_SHARE.meter();
            return values.anyAlternativeAdmits((position, set) -> {
                Carrier carrier = carriers.get(position);
                return carrier == null ? Emptiness.NONEMPTY
                        : carrier.meets(set, ordered.at(position), meter);
            });
        }

        /**
         * Whether the two readings hold nothing between them though neither of them holds nothing.
         *
         * <p>What tells this refusal from the two it is written beside. A position whose ends cross
         * is the order's own answer and a reading that admits nothing is the values', and each of
         * those is said as itself; this is the one nothing said until the two were put together.
         */
        boolean holdNothingOnlyTogether() {
            return !ordered.isBottom() && !valuesAloneHoldNothing()
                    && ofTheValues() == Emptiness.EMPTY;
        }

        /** Whether the values admit nothing before they are asked where the positions stop, which
         *  is the walk with nothing to ask. */
        private boolean valuesAloneHoldNothing() {
            return values.anyAlternativeAdmits((_, _) -> Emptiness.NONEMPTY) == Emptiness.EMPTY;
        }

        /**
         * The positions every alternative is left no value at by its set and its range together.
         *
         * <p>Empty where there is none to name, which is what a choice failing at two positions
         * leaves: each of them holds values some alternative stands at, and the lack is the whole
         * product's.
         */
        Set<A> sharingNothingAt() {
            if (ordered.isBottom()) {
                return Set.of();
            }
            Meter meter = PatternPlan.Budget.OF_WHAT_A_SET_AND_A_RANGE_SHARE.meter();
            return values.refusedInEveryAlternativeAt((position, set) -> {
                Carrier carrier = carriers.get(position);
                return carrier == null ? Emptiness.NONEMPTY
                        : carrier.meets(set, ordered.at(position), meter);
            });
        }

        /** What the values leave. These are worked out already, so there is nothing further to
         *  build and the answer is the one above. */
        @Override
        public Emptiness ofTheValuesAlreadyBuilt(Allowance<A> by) {
            return ofTheValues();
        }

        /** Both readings holding at once, in both languages. */
        OfAConjunction<A> meet(OfAConjunction<A> other) {
            Map<A, Carrier> both = new LinkedHashMap<>(carriers);
            both.putAll(other.carriers);
            return new OfAConjunction<>(values.meet(other.values), ordered.meet(other.ordered),
                    both);
        }

        /** The same rules about the same positions, under the names {@code naming} gives them. */
        <B> OfAConjunction<B> renamed(Function<A, B> naming) {
            Map<B, Carrier> out = new LinkedHashMap<>();
            carriers.forEach((position, carrier) -> out.put(naming.apply(position), carrier));
            return new OfAConjunction<>(values.renamed(naming), ordered.renamed(naming), out);
        }

        /** The same, with these values in place of what nothing read leaves. */
        OfAConjunction<A> withValues(ConjoinedAdmissibleValues<A> read) {
            return new OfAConjunction<>(read, ordered, carriers);
        }

        /** The same, with {@code bounded} taken as holding of the positions it bounds, on the
         *  orders {@code on} says they are counted by. */
        OfAConjunction<A> taking(OrderedIntervals<A> bounded, Map<A, Carrier> on) {
            Map<A, Carrier> both = new LinkedHashMap<>(carriers);
            both.putAll(on);
            return new OfAConjunction<>(values, ordered.meet(bounded), both);
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof OfAConjunction<?> it && values.equals(it.values)
                    && ordered.equals(it.ordered) && carriers.equals(it.carriers);
        }

        @Override
        public int hashCode() {
            return Objects.hash(values, ordered, carriers);
        }

        @Override
        public String toString() {
            return values + " within " + ordered;
        }
    }
}
