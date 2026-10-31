package souther.compiler.numeric;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
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

        /**
         * The ends found, each of them at least as tight as the one it came in with, and the
         * half-spaces the holes came to.
         *
         * <p>The half-spaces are the same facts the ends were drawn from, kept as statements about
         * the forms they are on. A bound on each position of {@code a + b} does not say how far
         * {@code a + b} itself runs, so a reader asking that has to be given the half-space.
         *
         * @param sided the half-spaces the holes came to against the state this round started in,
         *              each with its bound already moved onto what its form can reach. A set: which
         *              rule arrived first is not part of what they come to
         */
        record Tightened<A>(Map<A, ExactCut> atLeast, Map<A, ExactCut> atMost,
                            Set<AffineConstraint.HalfSpace<A>> sided)
                implements Reduction<A> {

            public Tightened {
                atLeast = Map.copyOf(atLeast);
                atMost = Map.copyOf(atMost);
                sided = Collections.unmodifiableSet(new LinkedHashSet<>(sided));
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
     * Every bound the rules put on a position given {@code given}, read once each against the same
     * state, with the holes among them settled first ({@link #settle}).
     *
     * @param given       the rules to read this way, the ends the round started in, and the one
     *                    reading of how far a form runs under them. Ends and relations both, because
     *                    the rest of a rule is a sum and a sum is bounded by things no position's own
     *                    ends carry. Rules the difference bounds already hold in full can be among
     *                    them and cost a little; ones of no shape at all are skipped
     * @param spacing     how each position's values are spaced, for the reason
     *                    {@link AffineConstraint#of} wants it
     */
    public static <A> Reduction<A> over(FormReach<A> given, Function<A, Granularity> spacing,
                                        CanonicalOrder<A> order) {
        Settled<A> settled = settle(given, spacing);
        if (settled == null) {
            return new Reduction.NothingIsLeft<>();
        }
        FormReach<A> reading = settled.reading();
        Box<A> from = reading.ends();
        List<AffineConstraint<A>> constraints = reading.rules();
        Map<A, ExactCut> atLeast = new LinkedHashMap<>();
        Map<A, ExactCut> atMost = new LinkedHashMap<>();
        // Per form the tightest bound only: two holes on one sum come to two bounds on it, and the
        // looser is held by the tighter.
        Map<CanonicalForm<A>, ExactCut> sided = new LinkedHashMap<>();
        settled.sidedOf().values().forEach(halves -> halves.forEach(
                half -> sided.merge(half.form(), half.bound(), ExactCut::tighterUpper)));
        for (AffineConstraint<A> each : constraints) {
            List<AffineConstraint.HalfSpace<A>> halves = each instanceof
                    AffineConstraint.Disequality<A> hole
                    ? settled.sidedOf().getOrDefault(hole, List.of()) : each.halfSpaces();
            for (AffineConstraint.HalfSpace<A> half : halves) {
                // Walked in the one order the positions decide. A bound worked out at each of them
                // is written into a reading the next of them is read against, so what this takes
                // first reaches the answer.
                for (A atom : half.form().atomsIn(order)) {
                    if (!record(half, atom, from, reading, each, spacing, atLeast, atMost)) {
                        return new Reduction.NothingIsLeft<>();
                    }
                }
            }
        }
        Set<AffineConstraint.HalfSpace<A>> tightest = new LinkedHashSet<>();
        sided.forEach((form, bound) -> tightest.add(new AffineConstraint.HalfSpace<>(form, bound)));
        return new Reduction.Tightened<>(atLeast, atMost, tightest);
    }

    /**
     * The holes among the rules, each settled that can be, and the reading they were settled
     * against.
     *
     * <p>Which side a hole falls on is not an approximation that more rounds make better. A hole
     * that has a side keeps it for as long as the state only narrows, and there are as many holes
     * as were said. So the holes are settled to the end here and not one step a round, beside the
     * rounds that narrow the ends: a run of holes on one sum — {@code f /= 50}, {@code f /= 49},
     * {@code f /= 48} — has each one's side decided by the one before it, and a run longer than the
     * rounds would otherwise stop part way.
     *
     * <p>Every pass asks the holes still open of one reading, the way every other rule is read
     * against one state, and the next pass reads what that one found beside it. A pass that settles
     * nothing is the last, and each pass before it settles a hole, so this stops after as many
     * passes as there are holes.
     *
     * @return null where a hole's sum is pinned at the value it is held away from
     */
    private static <A> Settled<A> settle(FormReach<A> given, Function<A, Granularity> spacing) {
        List<AffineConstraint.Disequality<A>> open = new ArrayList<>();
        for (AffineConstraint<A> each : given.rules()) {
            if (each instanceof AffineConstraint.Disequality<A> hole) {
                open.add(hole);
            }
        }
        Map<AffineConstraint.Disequality<A>, List<AffineConstraint.HalfSpace<A>>> sidedOf =
                new LinkedHashMap<>();
        FormReach<A> reading = given;
        Map<CanonicalForm<A>, ExactCut> known = new LinkedHashMap<>();
        given.derived().forEach(half -> known.merge(half.form(), half.bound(), ExactCut::tighterUpper));
        if (!known.isEmpty()) {
            List<AffineConstraint.Disequality<A>> unsettled = new ArrayList<>();
            for (AffineConstraint.Disequality<A> hole : open) {
                List<AffineConstraint.HalfSpace<A>> halves = alreadySided(hole, known, spacing);
                if (halves.isEmpty()) {
                    unsettled.add(hole);
                } else {
                    sidedOf.put(hole, halves);
                }
            }
            open = unsettled;
        }
        while (!open.isEmpty()) {
            Map<AffineConstraint.Disequality<A>, List<AffineConstraint.HalfSpace<A>>> found =
                    new LinkedHashMap<>();
            List<AffineConstraint.Disequality<A>> stillOpen = new ArrayList<>();
            for (List<AffineConstraint.Disequality<A>> onOneSum : onOneSumEach(open)) {
                if (!settleOnOneSum(onOneSum, reading, spacing, found, stillOpen)) {
                    return null;
                }
            }
            if (found.isEmpty()) {
                break;
            }
            sidedOf.putAll(found);
            List<AffineConstraint.HalfSpace<A>> more = new ArrayList<>();
            found.values().forEach(more::addAll);
            reading = reading.alsoReading(more);
            open = stillOpen;
        }
        return new Settled<>(reading, sidedOf);
    }

    /**
     * {@code holes} grouped by the sum they are on, in the order the first of each was said.
     *
     * <p>{@code f /= v} and {@code -f /= -v} are one rule ({@link AffineConstraint.Disequality}), so
     * they are on one sum and in one group, each written the way the first of the group was. The
     * hole kept is equal to the one said, so what is found for it is found for that one.
     */
    private static <A> Collection<List<AffineConstraint.Disequality<A>>> onOneSumEach(
            List<AffineConstraint.Disequality<A>> holes) {
        Map<CanonicalForm<A>, List<AffineConstraint.Disequality<A>>> grouped = new LinkedHashMap<>();
        for (AffineConstraint.Disequality<A> hole : holes) {
            List<AffineConstraint.Disequality<A>> there = grouped.get(hole.form());
            AffineConstraint.Disequality<A> written = hole;
            if (there == null) {
                there = grouped.get(hole.form().negated());
                written = new AffineConstraint.Disequality<>(hole.form().negated(), hole.at().negated());
            }
            if (there == null) {
                there = new ArrayList<>();
                grouped.put(hole.form(), there);
                written = hole;
            }
            there.add(written);
        }
        return grouped.values();
    }

    /**
     * The holes on one sum, settled against one asking of how far the sum runs.
     *
     * <p>What a hole settled on this sum says of the sum is read straight off its half-space, and
     * the next hole on it is held to that: {@code f /= 50} putting {@code f} at 49 or below is what
     * lets {@code f /= 49} put it at 48, and asking {@link FormReach} again for each step of such a
     * run would ask it once per hole. The answer is the same as asking again — the half-space is the
     * very premise that asking would take — and what asking could find besides, from the other sums,
     * is found by the next pass.
     *
     * <p>Run until no hole on the sum settles, which is as many times round as there are holes, and
     * in whatever order they come: each settles for the same reason when the sum has come far enough.
     *
     * @return false where a hole's sum is pinned at the value it is held away from
     */
    private static <A> boolean settleOnOneSum(
            List<AffineConstraint.Disequality<A>> holes, FormReach<A> reading,
            Function<A, Granularity> spacing,
            Map<AffineConstraint.Disequality<A>, List<AffineConstraint.HalfSpace<A>>> found,
            List<AffineConstraint.Disequality<A>> stillOpen) {
        Reach reach = reading.of(holes.getFirst().form().coefs(), ExactRatio.ZERO);
        List<AffineConstraint.Disequality<A>> pending = new ArrayList<>(holes);
        boolean progress = true;
        while (progress) {
            progress = false;
            for (Iterator<AffineConstraint.Disequality<A>> each = pending.iterator(); each.hasNext();) {
                AffineConstraint.Disequality<A> hole = each.next();
                List<AffineConstraint.HalfSpace<A>> halves = sidedBy(hole, reach, spacing);
                if (halves == null) {
                    return false;
                }
                if (!halves.isEmpty()) {
                    found.put(hole, halves);
                    reach = narrowedBy(reach, halves, hole.form());
                    each.remove();
                    progress = true;
                }
            }
        }
        stillOpen.addAll(pending);
        return true;
    }

    /** {@code reach} of {@code form} with what {@code halves} say of it: a half-space on the form
     *  bounds it above, and one on its negation bounds it below. */
    private static <A> Reach narrowedBy(Reach reach, List<AffineConstraint.HalfSpace<A>> halves,
                                        CanonicalForm<A> form) {
        ExactCut least = reach.least();
        ExactCut most = reach.most();
        for (AffineConstraint.HalfSpace<A> half : halves) {
            if (half.form().equals(form)) {
                most = ExactCut.tighterUpper(most, half.bound());
            } else {
                least = ExactCut.tighterLower(least,
                        new ExactCut(half.bound().at().negated(), half.bound().inclusive()));
            }
        }
        return new Reach(least, most);
    }

    /** The reading the holes were settled against, and the half-spaces each settled hole came to. */
    private record Settled<A>(
            FormReach<A> reading,
            Map<AffineConstraint.Disequality<A>, List<AffineConstraint.HalfSpace<A>>> sidedOf) {}

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
     * <p>The hole is not a premise of its own question: a disequality states no half-space
     * ({@link AffineConstraint#halfSpaces}). What the holes settled before it are, and they are
     * implied by the rules, so reading them cannot admit less than the rules do.
     *
     * <p>The bound is moved onto what the sum can reach, the way every other rule's is
     * ({@link AdditiveImage#tightenUpper}): beside a reach of at most 50, {@code f /= 50} over whole
     * numbers is {@code f <= 49}, and over a dense range it stays {@code f < 50}.
     *
     * @return the half-spaces it comes to, empty where the sum can still fall either side, or null
     *         where the sum is pinned at the very value it is held away from
     */
    private static <A> List<AffineConstraint.HalfSpace<A>> sidedBy(
            AffineConstraint.Disequality<A> hole, Reach reach, Function<A, Granularity> spacing) {
        ExactRatio away = hole.at();
        boolean neverBelow = reach.least() != null && reach.least().at().compareTo(away) >= 0;
        boolean neverAbove = reach.most() != null && reach.most().at().compareTo(away) <= 0;
        if (neverBelow && neverAbove
                && reach.least().at().equals(away) && reach.most().at().equals(away)
                && reach.least().inclusive() && reach.most().inclusive()) {
            return null;   // the sum is held at the one value it is held away from
        }
        if (neverBelow) {
            return List.of(aboveIt(hole, spacing));
        }
        if (neverAbove) {
            return List.of(belowIt(hole, spacing));
        }
        return List.of();
    }

    /** The half-space a hole comes to where the sum is known not to go below the value it is held
     *  away from. It depends on the hole and the spacing and on nothing that is known. */
    private static <A> AffineConstraint.HalfSpace<A> aboveIt(AffineConstraint.Disequality<A> hole,
                                                             Function<A, Granularity> spacing) {
        CanonicalForm<A> below = hole.form().negated();
        return new AffineConstraint.HalfSpace<>(below,
                below.imageOver(spacing).tightenUpper(ExactCut.exclusive(hole.at().negated())));
    }

    /** The half-space a hole comes to where the sum is known not to go above the value it is held
     *  away from. */
    private static <A> AffineConstraint.HalfSpace<A> belowIt(AffineConstraint.Disequality<A> hole,
                                                             Function<A, Granularity> spacing) {
        return new AffineConstraint.HalfSpace<>(hole.form(),
                hole.form().imageOver(spacing).tightenUpper(ExactCut.exclusive(hole.at())));
    }

    /**
     * Whether what an earlier reading derived already puts the sum on one side of the hole, and the
     * half-space that comes to if so.
     *
     * <p>A side, once decided, is kept while the state only narrows, and the bound it comes to is
     * the hole's and the spacing's alone. So a derived bound on the hole's form at least as tight as
     * that one says the sum is on that side already, and asking {@link FormReach} again would
     * return what is known.
     */
    private static <A> List<AffineConstraint.HalfSpace<A>> alreadySided(
            AffineConstraint.Disequality<A> hole, Map<CanonicalForm<A>, ExactCut> known,
            Function<A, Granularity> spacing) {
        for (AffineConstraint.HalfSpace<A> candidate : List.of(
                aboveIt(hole, spacing), belowIt(hole, spacing))) {
            ExactCut held = known.get(candidate.form());
            if (held != null && ExactCut.tighterUpper(held, candidate.bound()).equals(held)) {
                return List.of(candidate);
            }
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
                                      Map<A, ExactCut> atLeast, Map<A, ExactCut> atMost) {
        ExactRatio weight = half.form().coefs().get(atom);
        Least rest = leastOfTheRest(half, atom, reading, itsOwnRule);
        if (rest == null) {
            return true;   // some other position runs the wrong way without end, so nothing follows
        }
        // A model's own decimals can put the rest of the rule and this half-space's own bound far
        // enough apart in scale that the exact arithmetic cannot sum them. Nothing here follows for
        // this position then, same as an unbounded rest: derived once bounds only ever tighten, and a
        // derivation that could not be composed must never be read as `HoldsNever`, which would claim
        // the rules leave this position nothing.
        ExactRatio constant = rest.at().minus(half.bound().at()).orNull();
        if (constant == null) {
            return true;
        }
        // `k·a <= w - m`, which as a rule about `a` alone is `k·a + (m - w) <= 0`. Handed back to be
        // read as one, so that what it does with the rounding and with the values `a` can take is
        // what it does everywhere else.
        boolean strict = !half.bound().inclusive() || !rest.reached();
        AffineConstraint.Read<A> read = AffineConstraint.of(
                Map.of(atom, weight), constant,
                strict ? Rel.LT : Rel.LE, spacing);
        switch (read) {
            case AffineConstraint.Read.HoldsNever<A> _ -> {
                return false;
            }
            case AffineConstraint.Read.HoldsAlways<A> _ -> {
                return true;
            }
            // A rule this cannot write leaves this position no narrower, and is never read as the
            // rules leaving it nothing.
            case AffineConstraint.Read.NotWorkedOut<A> _ -> {
                return true;
            }
            case AffineConstraint.Read.Stated<A> stated
                    when stated.constraint() instanceof AffineConstraint.HalfSpace<A> alone -> {
                ExactCut cut = alone.bound();
                // A canonical one-position form weighs it by one or by minus one. Weighed by minus
                // one it reads `-a <= c`, which is `a >= -c` — the same cut on the other side of
                // nought, keeping whether the value itself is reached.
                if (alone.form().coefs().get(atom).signum() > 0) {
                    atMost.merge(atom, cut, ExactCut::tighterUpper);
                } else {
                    atLeast.merge(atom, new ExactCut(cut.at().negated(), cut.inclusive()),
                            ExactCut::tighterLower);
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
    private static <A> boolean holdsAValue(A atom, Box<A> from, Map<A, ExactCut> atLeast,
                                           Map<A, ExactCut> atMost) {
        ExactCut low = ExactCut.tighterLower(from.leastOf(atom), atLeast.get(atom));
        ExactCut high = ExactCut.tighterUpper(from.mostOf(atom), atMost.get(atom));
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
        Map<A, ExactRatio> rest = new LinkedHashMap<>(half.form().coefs());
        rest.remove(atom);
        ExactCut least = reading.leastOfTheRestOf(itsOwnRule, rest, ExactRatio.ZERO);
        return least == null ? null : new Least(least.at(), least.inclusive());
    }

    /** @param reached false where the sum comes arbitrarily close to {@code at} without arriving,
     *                 which makes what is derived from it strict */
    private record Least(ExactRatio at, boolean reached) {}
}
