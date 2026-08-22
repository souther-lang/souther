package souther.compiler.numeric;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

/**
 * What a rule over several positions leaves each of them, given what the others are left.
 *
 * <p>The part that was missing. A rule the difference bounds cannot hold —
 * {@code 300·straw + 600·choco <= 4800}, a sum of two lengths, anything weighing two positions
 * unevenly — was kept as written and read one way only: subtracted from a goal when something asked
 * whether the goal followed. Nothing ever read it the other way, so the range handed to everything
 * downstream was short of what the rules said, at every position such a rule names.
 *
 * <p>Read the other way it says this. Take {@code Σ cᵢ·xᵢ <= w} and one of its positions; move the
 * rest to the other side, and what is left bounds that position by however much of the budget the
 * rest cannot help taking:
 *
 * <pre>
 *     k·a  &lt;=  w - Σ(rest)      and      Σ(rest) &gt;= m
 *     k·a  &lt;=  w - m
 * </pre>
 *
 * <p>which is sound because it is arithmetic on what is already known — {@code m} is a lower bound
 * on the rest, so anything satisfying the rule satisfies this. And the last step, turning
 * {@code k·a <= w - m} into a bound on {@code a}, is not done here: it is handed back to
 * {@link AffineConstraint} as the one-position rule it is, so that the rounding, the strictness and
 * the tightening onto what {@code a} can actually take are the same ones every other rule gets. A
 * second implementation of that step is the one thing this must not have.
 *
 * <p><b>Three things it promises</b>, over a constraint {@code C} and a box {@code B}:
 *
 * <pre>
 *     reductive     what comes back is inside what went in
 *     sound         every point of B that satisfies C is inside what comes back
 *     monotone      a narrower box in, a no-wider box out
 * </pre>
 *
 * <p>The second is the whole of the work. A bound derived here that is not implied by the rules
 * refuses values a model admits, and no measure downstream is in a position to notice — which is why
 * it is checked against enumerated points rather than argued for.
 *
 * <p>Nothing here reaches anything but the state it was handed, which is the one the round started
 * in. It cannot ask what another rule found in the same round, so what it answers depends on that
 * state and the rule and nothing else — and putting the answers together afterwards is what keeps
 * the order the rules arrived in out of the result. What it may read of that state is both the ends
 * and the relations, because the rest of a rule is a sum and the thing that bounds a sum is often
 * not any one position's ends.
 */
public final class AffineReduction {

    private AffineReduction() {
    }

    /** What a round of reading the rules the other way found. */
    public sealed interface Reduction<A> {

        /** The ends found, each of them at least as tight as the one it came in with. */
        record Tightened<A>(Map<A, RationalCut> atLeast, Map<A, RationalCut> atMost)
                implements Reduction<A> {

            public Tightened {
                atLeast = Map.copyOf(atLeast);
                atMost = Map.copyOf(atMost);
            }
        }

        /**
         * A position was left no value at all, so nothing satisfies the rules together.
         *
         * <p>Said here rather than left for a reader to notice in the ends. A rule over several
         * positions can empty a system the difference bounds see nothing wrong with —
         * {@code x + y <= 5} beside {@code x >= 10} and {@code y >= 10} — and a reader handed two
         * ends that have crossed has to know to look.
         */
        record NothingIsLeft<A>() implements Reduction<A> {}
    }

    /**
     * Every bound the rules put on a position given {@code reading}, read once each against the same
     * state.
     *
     * @param reading     the rules to read this way, the ends the round started in, and the one
     *                    reading of how far a form runs under them. Ends and relations both, because
     *                    the rest of a rule is a sum and a sum is bounded by things no position's own
     *                    ends carry. Rules the difference bounds already hold in full can be among
     *                    them and cost a little; ones of no shape at all are skipped
     * @param spacing     how each position's values are spaced, for the reason
     *                    {@link AffineConstraint#of} wants it
     */
    public static <A> Reduction<A> over(FormReach<A> reading, Function<A, Granularity> spacing) {
        Box<A> from = reading.ends();
        List<AffineConstraint<A>> constraints = reading.rules();
        Map<A, RationalCut> atLeast = new LinkedHashMap<>();
        Map<A, RationalCut> atMost = new LinkedHashMap<>();
        for (AffineConstraint<A> each : constraints) {
            List<AffineConstraint.HalfSpace<A>> halves = each instanceof
                    AffineConstraint.Disequality<A> hole ? sidedBy(hole, reading) : each.halfSpaces();
            if (halves == null) {
                return new Reduction.NothingIsLeft<>();
            }
            for (AffineConstraint.HalfSpace<A> half : halves) {
                for (A atom : half.form().coefs().keySet()) {
                    if (!record(half, atom, from, reading, each, spacing, atLeast, atMost)) {
                        return new Reduction.NothingIsLeft<>();
                    }
                }
            }
        }
        return new Reduction.Tightened<>(atLeast, atMost);
    }

    /**
     * A hole turned into a bound, where what is known says which side of it the sum lies.
     *
     * <p>{@code f /= v} on its own bounds nothing: it says the sum is not one value, and a range
     * cannot leave one value out of the middle of itself. What it does say is this — if the sum is
     * already known not to go below {@code v}, then it goes above it, and if it is already known not
     * to go above, then it goes below. And where it is known to be exactly {@code v}, nothing is
     * left.
     *
     * <p>Asked of everything known, rather than of what happened to be known when the rule was read.
     * {@code x /= 0} beside {@code x >= 0} used to leave {@code x} at nought or above depending on
     * which of the two was written first, because the answer was decided at the moment the
     * disequality arrived and never revisited. Here it is decided against the same state every other
     * rule is read against, and again next round if that state has moved.
     *
     * <p>Everything known is {@link FormReach} and not the ends alone. A sum is held by things no
     * position's own range carries — a relation between two of them, a rule naming a third — and
     * asking the ends for it left a {@code guard} that wrote {@code /=} beside a relation stating
     * nothing, while the same {@code /=} beside a range on the value itself was read.
     *
     * <p>The hole cannot side itself. A disequality states no half-space
     * ({@link AffineConstraint#halfSpaces}), so it is not among what the reading may take as a
     * premise, and nothing here has to arrange for that.
     *
     * @return the half-spaces it comes to, empty where the sum can still fall either side, or null
     *         where the sum is pinned at the very value it is held away from
     */
    private static <A> List<AffineConstraint.HalfSpace<A>> sidedBy(
            AffineConstraint.Disequality<A> hole, FormReach<A> reading) {
        Reach reach = reading.of(hole.form().coefs(), Rational.ZERO);
        Rational away = hole.at();
        boolean neverBelow = reach.least() != null && reach.least().at().compareTo(away) >= 0;
        boolean neverAbove = reach.most() != null && reach.most().at().compareTo(away) <= 0;
        if (neverBelow && neverAbove
                && reach.least().at().equals(away) && reach.most().at().equals(away)
                && reach.least().inclusive() && reach.most().inclusive()) {
            return null;   // the sum is held at the one value it is held away from
        }
        if (neverBelow) {
            return List.of(new AffineConstraint.HalfSpace<>(
                    hole.form().negated(), RationalCut.exclusive(away.negated())));
        }
        if (neverAbove) {
            return List.of(new AffineConstraint.HalfSpace<>(
                    hole.form(), RationalCut.exclusive(away)));
        }
        return List.of();
    }

    /**
     * What one rule leaves one of its positions, written into {@code atLeast} / {@code atMost}.
     *
     * @return false where the rule leaves that position no value at all
     */
    private static <A> boolean record(AffineConstraint.HalfSpace<A> half, A atom, Box<A> from,
                                      FormReach<A> reading, AffineConstraint<A> itsOwnRule,
                                      Function<A, Granularity> spacing,
                                      Map<A, RationalCut> atLeast, Map<A, RationalCut> atMost) {
        Rational weight = half.form().coefs().get(atom);
        Least rest = leastOfTheRest(half, atom, reading, itsOwnRule);
        if (rest == null) {
            return true;   // some other position runs the wrong way without end, so nothing follows
        }
        // `k·a <= w - m`, which as a rule about `a` alone is `k·a + (m - w) <= 0`. Handed back to be
        // read as one, so that what it does with the rounding and with the values `a` can take is
        // what it does everywhere else.
        boolean strict = !half.bound().inclusive() || !rest.reached();
        AffineConstraint.Read<A> read = AffineConstraint.of(
                Map.of(atom, weight), rest.at().minus(half.bound().at()),
                strict ? NumericDomain.Rel.LT : NumericDomain.Rel.LE, spacing);
        switch (read) {
            case AffineConstraint.Read.HoldsNever<A> ignored -> {
                return false;
            }
            case AffineConstraint.Read.HoldsAlways<A> ignored -> {
                return true;
            }
            case AffineConstraint.Read.Stated<A> stated
                    when stated.constraint() instanceof AffineConstraint.HalfSpace<A> alone -> {
                RationalCut cut = alone.bound();
                // A canonical one-position form weighs it by one or by minus one. Weighed by minus
                // one it reads `-a <= c`, which is `a >= -c` — the same cut on the other side of
                // nought, keeping whether the value itself is reached.
                if (alone.form().coefs().get(atom).signum() > 0) {
                    atMost.merge(atom, cut, RationalCut::tighterUpper);
                } else {
                    atLeast.merge(atom, new RationalCut(cut.at().negated(), cut.inclusive()),
                            RationalCut::tighterLower);
                }
                return holdsAValue(atom, from, atLeast, atMost);
            }
            // A rule weighing one position is a bound on it, always. Said as a stop rather than left
            // to fall through, because the shape came back from the one place that decides shapes.
            case AffineConstraint.Read.Stated<A> stated -> throw new IllegalStateException(
                    "a rule about one position came back as " + stated.constraint());
        }
    }

    /**
     * Whether the ends now known at {@code atom} — the ones it came in with and the ones just found
     * — still leave it something.
     *
     * <p>The one thing here that reads what this round has found rather than what it started with.
     * It decides emptiness and nothing else: what is <em>derived</em> comes from the state the round
     * began in, so no bound depends on which rule was read first, while whether the rules have
     * emptied a position is noticed as soon as two ends cross rather than a round later. Worth
     * knowing when reading the promise above as "every rule sees the same state" — every rule
     * derives from the same state, which is not quite the same sentence.
     */
    private static <A> boolean holdsAValue(A atom, Box<A> from, Map<A, RationalCut> atLeast,
                                           Map<A, RationalCut> atMost) {
        RationalCut low = RationalCut.tighterLower(from.leastOf(atom), atLeast.get(atom));
        RationalCut high = RationalCut.tighterUpper(from.mostOf(atom), atMost.get(atom));
        if (low == null || high == null) {
            return true;
        }
        int order = low.at().compareTo(high.at());
        return order < 0 || (order == 0 && low.inclusive() && high.inclusive());
    }

    /**
     * The least the rest of the form can come to, and whether it can actually come to it.
     *
     * <p>Asked of {@link FormReach}, which is the one reading of how far a form runs. Summed from
     * each position's own ends and no further, this could not use a relation: under
     * {@code guard x >= y} the rest {@code x - y} has no end at either position, so a rule relating
     * it to a third was left bounding nothing at all — while the goal side, asking the very same
     * question of the very same state, read the relation and answered.
     *
     * <p>The rule being reduced is left out of the reading. It cannot make this unsound and it was
     * measured to change nothing, and what it would leave behind is a bound whose premise is the
     * rule it is a bound on.
     *
     * @return null where nothing bounds the rest below, which is where the rest can be made as small
     *         as you like and the rule bounds nothing
     */
    private static <A> Least leastOfTheRest(AffineConstraint.HalfSpace<A> half, A atom,
                                            FormReach<A> reading, AffineConstraint<A> itsOwnRule) {
        Map<A, Rational> rest = new LinkedHashMap<>(half.form().coefs());
        rest.remove(atom);
        RationalCut least = reading.ofTheRestOf(itsOwnRule, rest, Rational.ZERO).least();
        return least == null ? null : new Least(least.at(), least.inclusive());
    }

    /** @param reached false where the sum comes arbitrarily close to {@code at} without arriving,
     *                 which makes what is derived from it strict */
    private record Least(Rational at, boolean reached) {}
}
