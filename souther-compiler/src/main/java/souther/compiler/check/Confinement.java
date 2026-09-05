package souther.compiler.check;

import souther.compiler.numeric.OrderedIntervals;
import souther.compiler.regex.Meter;
import souther.compiler.regex.PatternPlan;
import souther.compiler.values.AdmissibleValues;
import souther.compiler.values.Allowance;
import souther.compiler.values.AskedOfEachPosition;
import souther.compiler.values.ConjoinedAdmissibleValues;
import souther.compiler.values.Emptiness;
import souther.compiler.values.PlannedValues;
import souther.compiler.values.Realized;
import souther.compiler.values.UnreadReason;
import souther.compiler.values.ValueSet;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.Function;

/**
 * Which values the positions of one value may take and where their orders stop, as one answer.
 *
 * <p>Two readings and one question. Which values a position may hold is a set, and where its order
 * stops is a range, and neither has a word for what the other holds — a pattern names no ends and an
 * ordering names no finite set. So a clause reaches whichever of them can say something about it,
 * and whether anything satisfies the rules is about the two of them together.
 *
 * <p><b>Which is why nothing else holds them side by side.</b> Asked of each in turn, the answer is
 * that something exists whenever the reading that was asked had nothing to say about the rules, and
 * that sentence was written in five places. Forbidding the spelling leaves a sixth to be written; so
 * the halves are not separately in hand, and the question has one implementation
 * ({@link #admitted}) that no holder can answer around.
 *
 * <p><b>Nothing is admitted where the ranges refuse every alternative, and something is admitted
 * only where they were asked.</b> That asymmetry is the whole of what went wrong. Either half
 * holding nothing leaves the pair nothing, so {@link Emptiness#EMPTY} is sound from either of them;
 * {@link Emptiness#NONEMPTY} is a claim about the pair and can only come out of the walk that was
 * handed the ranges. A reading that answered it from the values alone settled a branch as one
 * somebody can be in before anything asked where its positions stop.
 *
 * <p>What is not promised is that a pair nothing showed empty holds anything. The other domains of
 * {@link ConstraintState} are outside this and stay outside it: a reduction between the numbers and
 * an order is another one of these, added the same way, and calling this the whole of a
 * conjunction's satisfiability would be a claim the reductions in it do not carry.
 *
 * @param <A> what a position is called
 */
sealed interface Confinement<A> {

    /** Whether anything satisfies both readings. */
    Emptiness admits();

    /** Whether it is settled that nothing does. */
    default boolean holdsNothing() {
        return admits() == Emptiness.EMPTY;
    }

    /** What each position is ordered on, which is what a range and a set of values are put
     *  together over. */
    Map<A, Carrier> carriers();

    /**
     * The one implementation of the question, whatever the values are held as.
     *
     * <p>The ranges reach every position of every alternative, so what comes back is about the pair
     * — which is what makes {@link Emptiness#NONEMPTY} sayable at all. A holder whose values are
     * still descriptions answers as much of it as needs no machine and leaves the rest open; a
     * holder whose values are sets answers all of it.
     *
     * <p>A position on no order is one nothing here can refuse: what it admits is a set and there is
     * no range to share a value with.
     */
    static <A> Emptiness admitted(OrderedIntervals<A> ordered, Map<A, Carrier> carriers,
                                  Function<AskedOfEachPosition<A>, Emptiness> alternatives) {
        if (ordered.isBottom()) {
            return Emptiness.EMPTY;
        }
        // A meter of this question's own, spent on this asking of it. What may be built to decide
        // whether a declaration has a value cannot come out of a position's allowance: the same
        // rules would then be decided differently depending on what the readings before them had
        // already built.
        Meter meter = PatternPlan.Budget.OF_WHAT_A_SET_AND_A_RANGE_SHARE.meter();
        return alternatives.apply((position, set) -> {
            Carrier carrier = carriers.get(position);
            return carrier == null ? Emptiness.NONEMPTY
                    : carrier.meets(set, ordered.at(position), meter);
        });
    }

    /** The positions every alternative is left no value at, out of the same walk. */
    static <A> Set<A> sharingNothingAt(OrderedIntervals<A> ordered, Map<A, Carrier> carriers,
                                       Function<AskedOfEachPosition<A>, Set<A>> alternatives) {
        if (ordered.isBottom()) {
            return Set.of();
        }
        Meter meter = PatternPlan.Budget.OF_WHAT_A_SET_AND_A_RANGE_SHARE.meter();
        return alternatives.apply((position, set) -> {
            Carrier carrier = carriers.get(position);
            return carrier == null ? Emptiness.NONEMPTY
                    : carrier.meets(set, ordered.at(position), meter);
        });
    }

    /** What each position is ordered on, both tables put together. */
    static <A> Map<A, Carrier> both(Map<A, Carrier> these, Map<A, Carrier> those) {
        if (these.isEmpty()) {
            return those;
        }
        if (those.isEmpty()) {
            return these;
        }
        Map<A, Carrier> out = new LinkedHashMap<>(these);
        out.putAll(those);
        return Collections.unmodifiableMap(out);
    }

    /**
     * A reading whose values are still descriptions, beside where its positions stop.
     *
     * <p>What a position admits is a plan and not a set, so a description nobody has worked out is
     * one this cannot ask the ranges about — and it says so rather than answering from the half it
     * can read. Nothing here builds: the budget the answer is bounded by is spent where the values
     * are worked out, and a reading that spent it to settle a branch would make what a declaration
     * costs depend on how its author bracketed it.
     */
    final class Planned<A> implements Confinement<A> {

        private final PlannedValues<A> values;
        private final OrderedIntervals<A> ordered;
        private final Map<A, Carrier> carriers;

        Planned(PlannedValues<A> values, OrderedIntervals<A> ordered, Map<A, Carrier> carriers) {
            this.values = values;
            this.ordered = ordered;
            this.carriers = Collections.unmodifiableMap(new LinkedHashMap<>(carriers));
        }

        /** Nothing read, so nothing ruled out. */
        static <A> Planned<A> top(Map<A, Carrier> carriers) {
            return new Planned<>(PlannedValues.top(), OrderedIntervals.top(), carriers);
        }

        PlannedValues<A> values() {
            return values;
        }

        @Override
        public Map<A, Carrier> carriers() {
            return carriers;
        }

        @Override
        public Emptiness admits() {
            return Confinement.admitted(ordered, carriers, values::anyAlternativeAdmits);
        }

        /**
         * The same question out of what something has already built.
         *
         * <p>For a caller deciding whether to keep a branch while a reading is still being put
         * together. What it may spend is the answer's own allowance, so what is asked is what is
         * established and a branch nothing established is kept.
         */
        Emptiness alreadyEstablished(Allowance<A> by) {
            Emptiness said = admits();
            if (said != Emptiness.UNDECIDED) {
                return said;
            }
            return values.holdsNothingAsBuilt(by) ? Emptiness.EMPTY : Emptiness.UNDECIDED;
        }

        /** Both readings holding at once. */
        Planned<A> meet(Planned<A> other) {
            return new Planned<>(values.meet(other.values), ordered.meet(other.ordered),
                    Confinement.both(carriers, other.carriers));
        }

        /** Either of them, as each reading says it. */
        Planned<A> either(Planned<A> other, boolean apart) {
            return new Planned<>(
                    apart ? values.joinApart(other.values) : values.join(other.values),
                    ordered.join(other.ordered),
                    Confinement.both(carriers, other.carriers));
        }

        /** This, taken as holding nothing at all. */
        Planned<A> leavingNothing() {
            return new Planned<>(values.leavingNothing(), ordered.leavingNothing(), carriers);
        }

        /** Two branches neither of which anybody can be in, said as that. */
        Planned<A> bothDead(Planned<A> other) {
            return new Planned<>(values.leavingNothing().bothDead(other.values.leavingNothing()),
                    ordered.join(other.ordered), Confinement.both(carriers, other.carriers));
        }

        /** This, holding what working it out could not build. */
        Planned<A> alsoStanding(Map<A, List<UnreadReason>> standing) {
            return new Planned<>(values.alsoStanding(standing), ordered, carriers);
        }

        /** The values worked out, under {@code by}, and the same ranges beside them. */
        Worked<A> resolve(Allowance<A> by) {
            return new Worked<>(values.resolve(by), ordered, carriers);
        }

        @Override
        public String toString() {
            return values + " within " + ordered;
        }
    }

    /**
     * A reading whose values have been worked out, beside where its positions stop.
     *
     * <p>The sets are in hand, so every alternative can be asked where its positions stop and the
     * answer is settled either way.
     */
    final class Worked<A> implements Confinement<A> {

        private final Realized<A> made;
        private final OrderedIntervals<A> ordered;
        private final Map<A, Carrier> carriers;

        Worked(Realized<A> made, OrderedIntervals<A> ordered, Map<A, Carrier> carriers) {
            this.made = made;
            this.ordered = ordered;
            this.carriers = Collections.unmodifiableMap(new LinkedHashMap<>(carriers));
        }

        /** A reading whose positions were all worked out, beside the ranges they stop at. */
        static <A> Worked<A> of(AdmissibleValues<A> values, OrderedIntervals<A> ordered,
                                Map<A, Carrier> carriers) {
            return new Worked<>(new Realized<>(values, Set.of(), List.of()), ordered, carriers);
        }

        Realized<A> made() {
            return made;
        }

        AdmissibleValues<A> values() {
            return made.values();
        }

        @Override
        public Map<A, Carrier> carriers() {
            return carriers;
        }

        @Override
        public Emptiness admits() {
            Emptiness said = Confinement.admitted(ordered, carriers,
                    made.values()::anyAlternativeAdmits);
            // A position nobody could build is one what stands there is wider than the rules, so a
            // pair the ranges did not refuse may still hold nothing. Settled empty is settled all
            // the same: a narrower reading refuses no less.
            return said == Emptiness.NONEMPTY && !made.unbuilt().isEmpty()
                    ? Emptiness.UNDECIDED : said;
        }

        /** The positions the order leaves no value at, for a reader writing down where. */
        Set<A> holdingNothing() {
            return ordered.holdingNothing();
        }

        @Override
        public String toString() {
            return made.values() + " within " + ordered;
        }
    }

    /**
     * The readings of several declarations' clauses, conjoined, beside where their orders stop.
     *
     * <p>What a caller relating values holds. The conjunction is kept factored, so an alternative of
     * it is one alternative of each factor side by side and the walk asks each factor's own.
     */
    final class Conjoined<A> implements Confinement<A> {

        private final ConjoinedAdmissibleValues<A> values;
        private final OrderedIntervals<A> ordered;
        private final Map<A, Carrier> carriers;

        Conjoined(ConjoinedAdmissibleValues<A> values, OrderedIntervals<A> ordered,
                  Map<A, Carrier> carriers) {
            this.values = values;
            this.ordered = ordered;
            this.carriers = Collections.unmodifiableMap(new LinkedHashMap<>(carriers));
        }

        /** Nothing read, so nothing ruled out. */
        static <A> Conjoined<A> top() {
            return new Conjoined<>(ConjoinedAdmissibleValues.top(), OrderedIntervals.top(),
                    Map.of());
        }

        ConjoinedAdmissibleValues<A> values() {
            return values;
        }

        @Override
        public Map<A, Carrier> carriers() {
            return carriers;
        }

        @Override
        public Emptiness admits() {
            return Confinement.admitted(ordered, carriers, values::anyAlternativeAdmits);
        }

        /**
         * Whether the two readings hold nothing between them though neither of them holds nothing.
         *
         * <p>What tells this refusal from the two it is written beside. A position whose ends cross
         * is the order's own answer and a reading that admits nothing is the values', and each of
         * those is said as itself; this is the one nothing said until the two were put together.
         */
        boolean holdNothingOnlyTogether() {
            return !ordered.isBottom()
                    && values.anyAlternativeAdmits((_, _) -> Emptiness.NONEMPTY)
                            != Emptiness.EMPTY
                    && admits() == Emptiness.EMPTY;
        }

        /** The positions the order leaves no value at. */
        Set<A> holdingNothing() {
            return ordered.holdingNothing();
        }

        /** The positions every alternative is left no value at by its set and its range together. */
        Set<A> sharingNothingAt() {
            return Confinement.sharingNothingAt(ordered, carriers,
                    values::refusedInEveryAlternativeAt);
        }

        /** Which values may stand at one position. */
        ValueSet at(A position) {
            return values.at(position);
        }

        /** Both conjunctions holding at once, in both languages. */
        Conjoined<A> meet(Conjoined<A> other) {
            return new Conjoined<>(values.meet(other.values), ordered.meet(other.ordered),
                    Confinement.both(carriers, other.carriers));
        }

        /** The same rules about the same positions, under the names {@code naming} gives them. */
        <B> Conjoined<B> renamed(Function<A, B> naming) {
            Map<B, Carrier> out = new LinkedHashMap<>();
            carriers.forEach((position, carrier) -> out.put(naming.apply(position), carrier));
            return new Conjoined<>(values.renamed(naming), ordered.renamed(naming), out);
        }

        /** The same, with these values in place of what nothing read leaves. */
        Conjoined<A> withValues(ConjoinedAdmissibleValues<A> read) {
            return new Conjoined<>(read, ordered, carriers);
        }

        /** The same, with {@code bounded} taken as holding of the positions it bounds, on the
         *  orders {@code on} says they are counted by. */
        Conjoined<A> taking(OrderedIntervals<A> bounded, Map<A, Carrier> on) {
            return new Conjoined<>(values, ordered.meet(bounded), Confinement.both(carriers, on));
        }

        /**
         * The same, with one declaration's reading taken in — both languages at once.
         *
         * <p>One call and not two. What a declaration's clauses left is one answer with two faces,
         * and taking it in a face at a time is what let a caller hold half of it: the values met
         * here and the ranges met somewhere else, with a state in between that says a value exists
         * because the half it was given does.
         *
         * <p>Met with what nothing read leaves rather than assigned, which is not the same answer. A
         * reading a choice reached across two positions promises nothing about whole values, and a
         * conjunction with one of those promises nothing anywhere.
         */
        Conjoined<A> taking(Worked<A> read, Allowance<A> sets) {
            // The allowance the reading was worked out under, and not a fresh one: what a later
            // reader builds out of it is more of the same answer at the same positions.
            //
            // Said once, and what stands here until it is said is what nothing read leaves. Saying
            // it twice would keep the second reading and drop the first without a word. An
            // assertion because a throw would be caught by the fail-open around the reading and
            // leave it silently dropped.
            assert !values.hasReadings()
                    : "the values of a state are read once, and these were read over " + values;
            return new Conjoined<>(
                    ConjoinedAdmissibleValues.of(
                            AdmissibleValues.<A>top().meet(read.values(), sets), sets),
                    ordered.meet(read.ordered), Confinement.both(carriers, read.carriers()));
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof Conjoined<?> it && values.equals(it.values)
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
