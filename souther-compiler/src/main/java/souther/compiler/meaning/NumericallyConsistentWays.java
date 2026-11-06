package souther.compiler.meaning;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Rel;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.OptionalLong;
import java.util.function.Function;

/**
 * How many of the ways of choosing a case of a line no comparison chosen on the way refutes, read
 * as numbers: the ways whose comparisons of one affine form some one value of the form meets, and
 * whose comparisons of remainders of one dividend some one remainder of it meets.
 *
 * <p>A count of ways of choosing, and not of cases there are or of work done. Two ways reaching
 * one case are two ways here, as they are to {@link DecidingCase.Cases#structuralWays}; and a
 * reader asking the cases does not walk these and only these, since it stops a choosing early or
 * at a figure. Every atom that is not such a comparison is taken to hold either way, and whether
 * a whole number meets a form is not asked, so the count is at least as many as the ways some row
 * can take: what it says is that no more than these can.
 *
 * <p><b>For a reader explaining a line, and nothing that reads the line.</b> Asking the cases is
 * {@link CasesOfALineAsked}'s; this counts beside it where a reader is told why it stopped, and no
 * figure it meets is one the line stopped at.
 *
 * <p><b>Counted by what is left, and not way by way.</b> What a way has chosen so far leaves each
 * form an interval and each dividend some of its remainders, and the ways past a case depend on
 * nothing else of what was chosen before it. So each case is worked out once for each state it is
 * reached in, with how many ways reach that state carried beside it, and the work is as many
 * states as the cases are reached in — not as many as the ways.
 */
public final class NumericallyConsistentWays {

    /**
     * How many states the cases may be reached in, counted over every case, before the count is
     * given up.
     *
     * <p>Not a figure a reading stops at: past it the line is what it was, and only the count is
     * not said.
     */
    public static final int STATES_A_COUNT_IS_TAKEN_IN = 1 << 16;

    /** Remainders past this divisor are not told apart, and a comparison of one leaves the
     *  dividend's remainders as they were. */
    private static final int MOST_REMAINDERS_TOLD_APART = Long.SIZE - 1;

    private NumericallyConsistentWays() {
    }

    /** What counting came to. */
    public sealed interface Counted {

        /** No more ways than {@code ways} are consistent. */
        record AtMost(BigInteger ways) implements Counted {

            public AtMost {
                if (ways == null || ways.signum() < 0) {
                    throw new IllegalArgumentException("a count of ways is some number of them");
                }
            }
        }

        /** Nothing is said of how many ways are consistent, for the reason {@code why}. */
        record NotCounted(WhyNotCounted why) implements Counted {

            public NotCounted {
                Objects.requireNonNull(why, "a count given up is given up for a reason");
            }
        }
    }

    /** Why a count was given up: neither is a figure the line stopped at. */
    public enum WhyNotCounted {

        /** More states were reached than {@link #STATES_A_COUNT_IS_TAKEN_IN}. */
        STATES_A_COUNT_IS_TAKEN_IN,

        /** More ways were consistent than {@link CaseCount#WAYS_A_COUNT_IS_HELD_TO}. */
        WAYS_A_COUNT_IS_HELD_TO
    }

    /** How many ways of choosing a case of {@code cases} no comparison chosen refutes. */
    public static Counted of(DecidingCase.Cases cases) {
        return of(cases, State.NOTHING_CHOSEN);
    }

    /** The same, of the ways that start where {@code start} leaves the numbers. */
    static Counted of(DecidingCase.Cases cases, State start) {
        Counting counting = new Counting();
        Map<State, BigInteger> out = cases.fold(counting).apply(start);
        if (counting.reached > STATES_A_COUNT_IS_TAKEN_IN) {
            return new Counted.NotCounted(WhyNotCounted.STATES_A_COUNT_IS_TAKEN_IN);
        }
        BigInteger ways = out.values().stream().reduce(BigInteger.ZERO, Counting::sum);
        return ways.compareTo(CaseCount.WAYS_A_COUNT_IS_HELD_TO) > 0
                ? new Counted.NotCounted(WhyNotCounted.WAYS_A_COUNT_IS_HELD_TO)
                : new Counted.AtMost(ways);
    }

    /**
     * What each case comes to from each state it is reached in: the states it leaves, each with
     * how many of its ways leave it. Each answer is kept, so a case reached again in one state is
     * not worked out again.
     */
    private static final class Counting
            implements DecidingCase.Cases.Fold<Function<State, Map<State, BigInteger>>> {

        private int reached;

        /** Past {@link CaseCount#WAYS_A_COUNT_IS_HELD_TO} a count is one past it, which says only
         *  that it is more; so no number worked out here is longer than that. */
        private static final BigInteger BEYOND = CaseCount.WAYS_A_COUNT_IS_HELD_TO.add(BigInteger.ONE);

        private static BigInteger sum(BigInteger one, BigInteger other) {
            return one.add(other).min(BEYOND);
        }

        private static BigInteger product(BigInteger one, BigInteger other) {
            return one.multiply(other).min(BEYOND);
        }

        private Function<State, Map<State, BigInteger>> remembered(
                Function<State, Map<State, BigInteger>> from) {
            Map<State, Map<State, BigInteger>> known = new HashMap<>();
            return state -> {
                Map<State, BigInteger> answer = known.get(state);
                if (answer != null) {
                    return answer;
                }
                // Past the figure nothing more is worked out: what was counted is said to be no
                // count at all.
                if (++reached > STATES_A_COUNT_IS_TAKEN_IN) {
                    return Map.of();
                }
                answer = from.apply(state);
                known.put(state, answer);
                return answer;
            };
        }

        @Override
        public Function<State, Map<State, BigInteger>> one(DecidingCase.Cases.One one) {
            List<Narrowing> parts = new ArrayList<>();
            conjunctsOf(one.condition()).forEach(part -> Narrowing.of(part).ifPresent(parts::add));
            return remembered(state -> {
                State left = state;
                for (Narrowing part : parts) {
                    left = left.taking(part);
                    if (left == null) {
                        return Map.of();
                    }
                }
                return Map.of(left, BigInteger.ONE);
            });
        }

        @Override
        public Function<State, Map<State, BigInteger>> eachOf(
                DecidingCase.Cases.EachOf node,
                List<Function<State, Map<State, BigInteger>>> alternatives) {
            return remembered(state -> {
                Map<State, BigInteger> out = new HashMap<>();
                for (Function<State, Map<State, BigInteger>> alternative : alternatives) {
                    alternative.apply(state).forEach((left, ways) ->
                            out.merge(left, ways, Counting::sum));
                }
                return out;
            });
        }

        @Override
        public Function<State, Map<State, BigInteger>> together(
                DecidingCase.Cases.Together node,
                List<Function<State, Map<State, BigInteger>>> factors) {
            return remembered(state -> {
                Map<State, BigInteger> sofar = Map.of(state, BigInteger.ONE);
                for (Function<State, Map<State, BigInteger>> factor : factors) {
                    Map<State, BigInteger> next = new HashMap<>();
                    sofar.forEach((before, ways) -> factor.apply(before).forEach((left, more) ->
                            next.merge(left, product(ways, more), Counting::sum)));
                    if (next.isEmpty()) {
                        return Map.of();
                    }
                    sofar = next;
                }
                return sofar;
            });
        }

        @Override
        public Function<State, Map<State, BigInteger>> notTakenApart(
                DecidingCase.Cases.NotTakenApart notTakenApart) {
            return state -> Map.of(state, BigInteger.ONE);
        }
    }

    /**
     * The remainders of its dividend {@code part} holds at, as bits, where it compares a
     * remainder of one dividend this tells apart; none where it does not. The same reading of a
     * remainder's comparison a count takes.
     */
    static OptionalLong remaindersWhereItHolds(Proposition part) {
        Optional<Remainders> meeting = Narrowing.of(part).flatMap(Narrowing::remainders);
        return meeting.isEmpty() ? OptionalLong.empty()
                : OptionalLong.of(meeting.get().allowed());
    }

    /** What a condition chosen states together: its parts, where it is a conjunction. */
    private static List<Proposition> conjunctsOf(Proposition condition) {
        if (condition instanceof Proposition.All all) {
            List<Proposition> out = new ArrayList<>();
            all.parts().forEach(one -> out.addAll(conjunctsOf(one)));
            return out;
        }
        return condition instanceof Proposition.Always ? List.of() : List.of(condition);
    }

    /**
     * What one affine form is left: the values from {@code low} to {@code high}, each end in or
     * out and absent where nothing bounds that side, and none of {@code not}.
     *
     * @param not values the form is not, each within the ends, in rising order
     */
    record Interval(ExactRatio low, boolean lowOpen, ExactRatio high, boolean highOpen,
                    List<ExactRatio> not) {

        static final Interval EVERY = new Interval(null, false, null, false, List.of());

        Interval {
            not = List.copyOf(not);
        }

        /** This, with the form in {@code rel} to {@code at}; null where that leaves no value. */
        Interval with(Rel rel, ExactRatio at) {
            Interval out = switch (rel) {
                case GE, GT -> above(at, rel == Rel.GT);
                case LE, LT -> below(at, rel == Rel.LT);
                case EQ -> admits(at) ? new Interval(at, false, at, false, List.of()) : null;
                case NE -> not.contains(at) ? this : without(at);
            };
            return out == null || out.empty() ? null : out.trimmed();
        }

        private Interval above(ExactRatio at, boolean open) {
            int against = low == null ? 1 : at.compareTo(low);
            return against > 0 || (against == 0 && open)
                    ? new Interval(at, open, high, highOpen, not) : this;
        }

        private Interval below(ExactRatio at, boolean open) {
            int against = high == null ? -1 : at.compareTo(high);
            return against < 0 || (against == 0 && open)
                    ? new Interval(low, lowOpen, at, open, not) : this;
        }

        private Interval without(ExactRatio at) {
            List<ExactRatio> more = new ArrayList<>(not);
            more.add(at);
            more.sort(ExactRatio::compareTo);
            return new Interval(low, lowOpen, high, highOpen, more);
        }

        private boolean admits(ExactRatio at) {
            return within(at) && !(low != null && lowOpen && at.compareTo(low) == 0)
                    && !(high != null && highOpen && at.compareTo(high) == 0)
                    && !not.contains(at);
        }

        private boolean within(ExactRatio at) {
            return (low == null || at.compareTo(low) >= 0)
                    && (high == null || at.compareTo(high) <= 0);
        }

        private boolean empty() {
            if (low == null || high == null) {
                return false;
            }
            int against = low.compareTo(high);
            return against > 0 || (against == 0 && (lowOpen || highOpen || not.contains(low)));
        }

        /** The same values, with no value it is not kept where the ends leave it out anyway. */
        private Interval trimmed() {
            List<ExactRatio> kept = not.stream().filter(this::within).toList();
            return kept.size() == not.size() ? this
                    : new Interval(low, lowOpen, high, highOpen, kept);
        }
    }

    /**
     * The coefficients of an affine form, hashed once: a state is looked up by its forms at every
     * case it reaches, and a form's coefficients hash every quantity in them.
     */
    private record Form(Map<Quantity, ExactRatio> coefs, int hash) {

        Form(Map<Quantity, ExactRatio> coefs) {
            this(coefs, coefs.hashCode());
        }

        @Override
        public boolean equals(Object other) {
            return this == other || (other instanceof Form form && hash == form.hash
                    && coefs.equals(form.coefs));
        }

        @Override
        public int hashCode() {
            return hash;
        }
    }

    /** A dividend's remainders, told apart by the form of the dividend and the divisor. */
    private record Dividend(Form form, int divisor) {
    }

    /** Which remainders of {@code of} a comparison leaves, as bits. */
    private record Remainders(Dividend of, long allowed) {
    }

    /**
     * One comparison of an affine form as it narrows a state, worked out once from the
     * proposition: the form is to be {@code rel} to {@code at}, and a remainder compared leaves its
     * dividend {@code remainders}, where it is one told apart.
     */
    private record Narrowing(Form form, Rel rel, ExactRatio at,
                             Optional<Remainders> remainders) {

        /** {@code part} as a narrowing; none where it compares no affine form, and so leaves
         *  every state as it was. */
        static Optional<Narrowing> of(Proposition part) {
            if (!(part instanceof Proposition.Compared(Relation.Affine affine, boolean holds,
                    Spelling _, var _)) || affine.form().coefs().isEmpty()) {
                return Optional.empty();
            }
            Map<Quantity, ExactRatio> form = affine.form().coefs();
            Optional<Remainders> remainders = Optional.empty();
            if (form.size() == 1 && form.keySet().iterator().next()
                    instanceof Quantity.RemainderOfADividend remainder
                    && remainder.divisor().compareTo(
                            BigInteger.valueOf(MOST_REMAINDERS_TOLD_APART)) <= 0) {
                int divisor = remainder.divisor().intValueExact();
                remainders = Optional.of(new Remainders(
                        new Dividend(new Form(remainder.dividend().coefs()), divisor),
                        remaindersMeeting(remainder, form.get(remainder),
                                affine.form().constant(), affine.proposition(), holds,
                                divisor)));
            }
            return Optional.of(new Narrowing(new Form(form),
                    holds ? affine.proposition() : affine.proposition().denied(),
                    affine.form().constant().negated(), remainders));
        }

        /**
         * Which remainders of the dividend's form without its constant meet the comparison, as
         * bits: the remainder compared is that one moved by the constant, round the divisor. A
         * remainder whose comparison the exact arithmetic cannot hold is kept, as is every one
         * where the constant is no whole number held, since keeping is what leaves the count a
         * bound.
         */
        private static long remaindersMeeting(Quantity.RemainderOfADividend remainder,
                                              ExactRatio by, ExactRatio constant, Rel rel,
                                              boolean holds, int divisor) {
            long every = (1L << divisor) - 1;
            BigInteger moved = remainder.dividend().constant().isWhole()
                    ? remainder.dividend().constant().floor().orNull() : null;
            if (moved == null) {
                return every;
            }
            long out = 0;
            for (int left = 0; left < divisor; left++) {
                int compared = BigInteger.valueOf(left).add(moved)
                        .mod(BigInteger.valueOf(divisor)).intValueExact();
                ExactRatio weighed = by.times(ExactRatio.of(compared)).orNull();
                ExactRatio at = weighed == null ? null : weighed.plus(constant).orNull();
                if (at == null || rel.holds(at.signum()) == holds) {
                    out |= 1L << left;
                }
            }
            return out;
        }
    }

    /**
     * What the comparisons chosen so far leave: each affine form's interval, and each dividend's
     * remainders as the bits of a number.
     *
     * <p>Hashed once when made, since every case a state reaches looks it up and every case
     * leaving it merges it, and each such hash would otherwise walk every form it holds.
     */
    static final class State {

        static final State NOTHING_CHOSEN = new State(Map.of(), Map.of());

        private final Map<Form, Interval> forms;
        private final Map<Dividend, Long> remainders;
        private final int hash;

        /** Held as given: each map is made for this state and changed by nobody after. */
        private State(Map<Form, Interval> forms, Map<Dividend, Long> remainders) {
            this.forms = forms;
            this.remainders = remainders;
            int hash = 0;
            for (Map.Entry<Form, Interval> each : forms.entrySet()) {
                hash += mixed(31 * each.getKey().hashCode() + each.getValue().hashCode());
            }
            for (Map.Entry<Dividend, Long> each : remainders.entrySet()) {
                hash += mixed(31 * each.getKey().hashCode() + each.getValue().hashCode());
            }
            this.hash = hash;
        }

        /**
         * One entry's hash spread over every bit. A map's own hash adds each key's hash bitwise
         * apart from its value's, and states giving a few forms one of two intervals each then
         * share a hash far more often than not.
         */
        private static int mixed(int entry) {
            int out = entry * 0x9E3779B9;
            out ^= out >>> 16;
            out *= 0x85EBCA6B;
            return out ^ (out >>> 13);
        }

        /** This with {@code part} chosen; null where it leaves a form or a dividend nothing. */
        State taking(Proposition part) {
            Optional<Narrowing> narrowing = Narrowing.of(part);
            return narrowing.isEmpty() ? this : taking(narrowing.get());
        }

        /** This with {@code part} chosen; null where it leaves a form or a dividend nothing. */
        private State taking(Narrowing part) {
            Interval left = forms.getOrDefault(part.form(), Interval.EVERY)
                    .with(part.rel(), part.at());
            if (left == null) {
                return null;
            }
            Map<Form, Interval> nextForms = new HashMap<>(forms);
            nextForms.put(part.form(), left);
            Map<Dividend, Long> nextRemainders = remainders;
            if (part.remainders().isPresent()) {
                Remainders meeting = part.remainders().get();
                long kept = remainders.getOrDefault(meeting.of(),
                        (1L << meeting.of().divisor()) - 1) & meeting.allowed();
                if (kept == 0) {
                    return null;
                }
                nextRemainders = new HashMap<>(remainders);
                nextRemainders.put(meeting.of(), kept);
            }
            return new State(nextForms, nextRemainders);
        }

        @Override
        public boolean equals(Object other) {
            return this == other || (other instanceof State state && hash == state.hash
                    && forms.equals(state.forms) && remainders.equals(state.remainders));
        }

        @Override
        public int hashCode() {
            return hash;
        }
    }
}
