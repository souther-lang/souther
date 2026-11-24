package souther.compiler.numeric;

import souther.compiler.collect.InTheOrderGiven;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * What the rules leave every position and every difference of two of them, closed.
 *
 * <p>One structure where there were three. A bound on a position and a bound on a difference were
 * kept apart — {@code lo}, {@code hi} and a table of differences — and read back by three routes
 * that had to agree: the tightest bound on a position, the tightest bound on a difference, and
 * whether the two could hold at once. The old code says as much where it asks whether anything is
 * left, that a difference cycle summing below zero and a lower bound above an upper one "are one
 * thing seen twice".
 *
 * <p>They are one thing because a bound is a difference from nought. Written that way —
 * {@code a <= 10} as {@code a - 0 <= 10}, {@code a >= 3} as {@code 0 - a <= -3} — every rule of this
 * shape is an edge between two nodes, one of which may be the nought this adds. Closing the edges
 * over each other then answers all three questions at once, and a contradiction is a cycle that
 * comes back below where it started.
 *
 * <p><b>Nought is gone through and not kept.</b> A path through nought is a bound above on the
 * position it leaves and a bound below on the one it reaches, so what it says of a difference is
 * {@code a - b <= hi(a) - lo(b)}: the two bounds, and nothing a reader holding them does not hold
 * already. Every bounded position has an edge to or from nought, so kept as a node it relates every
 * two of them, and the table it fills is as large as the square of the positions where the rules
 * relate few of them. So what is kept is the differences closed among the positions, which only the
 * rules relating two positions fill, and each position's bounds closed along them; a difference
 * through nought is worked out from the bounds where it is asked for ({@link #differenceBound}).
 *
 * <p><b>Complete for what it holds.</b> Closing a difference-bound system finds a negative cycle
 * exactly when one exists, so within this fragment "the rules leave nothing" and "this says the
 * rules leave nothing" are the same statement. That is not true of the algebra as a whole — a
 * general sum is held elsewhere and reasoned about approximately — so what holds overall is one
 * direction only: where this says nothing is left, nothing is.
 *
 * <p>Exact throughout. The edges are {@link ExactRatio}, and a bound only becomes a decimal somebody
 * can read at the edge where it is handed over. Closed on decimals rounded to a fixed number of
 * digits, a system with no solution comes back with one — the arithmetic that separates the two ends
 * of {@code 3a = 1} is finer than the rounding.
 */
public final class DifferenceBounds<A> {

    /**
     * {@code above - below <= by}, closed, along differences the rules state between two positions
     * and not through nought.
     */
    public record Apart<A>(A above, A below, ExactCut by) {}

    /** The closed differences among the positions, by the position each is taken from. A row's
     *  entry for its own position is a cycle. */
    private final Map<A, Map<A, ExactCut>> related;
    private final List<Apart<A>> relations;
    /** The closed {@code a - 0 <= w}: the tightest bound above each position. */
    private final Map<A, ExactCut> above;
    /** The closed {@code 0 - a <= w}: the tightest bound below each position, on the other side of
     *  nought. */
    private final Map<A, ExactCut> below;
    private final Set<A> positions;
    private final boolean holdsNothing;
    private final boolean everyHopWasComposed;

    private DifferenceBounds(Map<A, Map<A, ExactCut>> related, Map<A, ExactCut> above,
                             Map<A, ExactCut> below, Set<A> positions, boolean holdsNothing,
                             boolean everyHopWasComposed) {
        // Held for as long as the closure is, which is as long as what it answers is asked: kept
        // as the tables they were built in, each holds a table and an entry per position on top
        // of what it says.
        Map<A, Map<A, ExactCut>> rows = new LinkedHashMap<>();
        related.forEach((from, row) -> rows.put(from, InTheOrderGiven.map(row)));
        this.related = InTheOrderGiven.map(rows);
        this.above = InTheOrderGiven.map(above);
        this.below = InTheOrderGiven.map(below);
        this.positions = InTheOrderGiven.set(positions);
        this.holdsNothing = holdsNothing;
        this.everyHopWasComposed = everyHopWasComposed;
        List<Apart<A>> apart = new ArrayList<>();
        related.forEach((from, row) -> row.forEach((to, by) -> {
            if (!from.equals(to)) {
                apart.add(new Apart<>(from, to, by));
            }
        }));
        this.relations = List.copyOf(apart);
    }

    /**
     * The constraints of this shape among {@code constraints}, closed over each other.
     *
     * <p>Everything else is left where it is, and nothing has to sort the rules first: what is not
     * of this shape is skipped here and read by the reduction, and a rule of this shape is read by
     * both — exactly, here, and again as a plain sum there, which costs a little and says nothing
     * new. So there is one decision about the shape and it is made here.
     */
    public static <A> DifferenceBounds<A> over(Iterable<AffineConstraint<A>> constraints,
                                               CanonicalOrder<A> order) {
        Map<A, Map<A, ExactCut>> between = new LinkedHashMap<>();
        Map<A, ExactCut> above = new LinkedHashMap<>();
        Map<A, ExactCut> below = new LinkedHashMap<>();
        Set<A> positions = new LinkedHashSet<>();
        for (AffineConstraint<A> each : constraints) {
            for (Edge<A> edge : edgesOf(each, order)) {
                switch (edge) {
                    case Edge.Above<A> up -> {
                        positions.add(up.position());
                        above.merge(up.position(), up.at(), ExactCut::tighterUpper);
                    }
                    case Edge.Below<A> down -> {
                        positions.add(down.position());
                        below.merge(down.position(), down.at(), ExactCut::tighterUpper);
                    }
                    case Edge.Between<A> apart -> {
                        positions.add(apart.from());
                        positions.add(apart.to());
                        between.computeIfAbsent(apart.from(), k -> new LinkedHashMap<>())
                                .merge(apart.to(), apart.at(), ExactCut::tighterUpper);
                    }
                }
            }
        }
        return closing(between, above, below, positions);
    }

    /**
     * What {@link #over} comes to for the rules these were made from followed by {@code added}, or
     * null where that is not worked out from these alone.
     *
     * <p>Only where no rule so far relates two positions and none of {@code added} does: then there
     * is no path through any position, and what each bound comes to is the tightest of the rules
     * that state it. A rule that relates two positions makes a path of the rules before it and the
     * ones after, and is closed by {@link #over}.
     */
    DifferenceBounds<A> followedBy(List<AffineConstraint<A>> added, CanonicalOrder<A> order) {
        if (holdsNothing || !related.isEmpty()) {
            return null;
        }
        Map<A, ExactCut> aboveNow = new LinkedHashMap<>(above);
        Map<A, ExactCut> belowNow = new LinkedHashMap<>(below);
        Set<A> positionsNow = new LinkedHashSet<>(positions);
        Set<A> touched = new LinkedHashSet<>();
        for (AffineConstraint<A> each : added) {
            for (Edge<A> edge : edgesOf(each, order)) {
                switch (edge) {
                    case Edge.Above<A> up -> {
                        positionsNow.add(up.position());
                        touched.add(up.position());
                        aboveNow.merge(up.position(), up.at(), ExactCut::tighterUpper);
                    }
                    case Edge.Below<A> down -> {
                        positionsNow.add(down.position());
                        touched.add(down.position());
                        belowNow.merge(down.position(), down.at(), ExactCut::tighterUpper);
                    }
                    case Edge.Between<A> _ -> {
                        return null;
                    }
                }
            }
        }
        boolean nothing = false;
        for (A position : touched) {
            if (crossed(belowNow.get(position), aboveNow.get(position))) {
                nothing = true;
                break;
            }
        }
        if (nothing) {
            return new DifferenceBounds<>(Map.of(), Map.of(), Map.of(), positionsNow, true,
                    everyHopWasComposed);
        }
        return new DifferenceBounds<>(Map.of(), aboveNow, belowNow, positionsNow, false,
                everyHopWasComposed);
    }

    /**
     * Closures over positions no two of them share, as the one closure of all their rules.
     *
     * <p>No edge runs from one of them into another, so no path does either, and closing their
     * rules together composes exactly the hops each of them composed on its own. What is left is to
     * hold the tables side by side — all three of them, and not only the {@link #relations}: a
     * difference between positions of two of these is still answered through nought, out of one
     * position's bound above and the other's bound below ({@link #differenceBound}).
     *
     * @throws IllegalArgumentException where two of them say something about one position, which
     *         is a path from one into the other that neither of them closed
     */
    static <A> DifferenceBounds<A> product(List<DifferenceBounds<A>> parts) {
        // The tables are the parts' put side by side, so how many there will be is known before
        // the first is copied: held to that, none of them is grown while it is filled.
        int relatedSize = 0;
        int aboveSize = 0;
        int belowSize = 0;
        int positionsSize = 0;
        for (DifferenceBounds<A> part : parts) {
            relatedSize += part.related.size();
            aboveSize += part.above.size();
            belowSize += part.below.size();
            positionsSize += part.positions.size();
        }
        Map<A, Map<A, ExactCut>> related = LinkedHashMap.newLinkedHashMap(relatedSize);
        Map<A, ExactCut> above = LinkedHashMap.newLinkedHashMap(aboveSize);
        Map<A, ExactCut> below = LinkedHashMap.newLinkedHashMap(belowSize);
        Set<A> positions = LinkedHashSet.newLinkedHashSet(positionsSize);
        boolean holdsNothing = false;
        boolean everyHopWasComposed = true;
        for (DifferenceBounds<A> part : parts) {
            for (A position : part.positions) {
                if (!positions.add(position)) {
                    throw new IllegalArgumentException(
                            "`" + position + "` is in two of the closures being put together");
                }
            }
            related.putAll(part.related);
            above.putAll(part.above);
            below.putAll(part.below);
            holdsNothing |= part.holdsNothing;
            everyHopWasComposed &= part.everyHopWasComposed;
        }
        return new DifferenceBounds<>(related, above, below, positions, holdsNothing,
                everyHopWasComposed);
    }

    /** Whether this can hold what {@code constraint} says, in full — which is what the shapes above
     *  amount to, asked directly so that they can be pinned down. */
    static <A> boolean canHold(AffineConstraint<A> constraint, CanonicalOrder<A> order) {
        return !edgesOf(constraint, order).isEmpty();
    }

    /**
     * The edges one constraint states, which is none where it is not of this shape.
     *
     * <p>A canonical form's coefficients are whole numbers sharing nothing, so a form naming one
     * position weighs it by exactly one or minus one, and a form naming two is a difference exactly
     * where their weights are one of each. That is what makes {@code 2a <= 10} a bound on a position
     * here and {@code 2a - 2b <= 4} a difference: they are the same rules as {@code a <= 5} and
     * {@code a - b <= 2}, and were only ever a different shape because they had been read off the
     * coefficients as they were typed.
     *
     * <p>Which half-spaces a constraint states is the constraint's own answer, so an equality being
     * a bound above and a bound below is not restated here. Either every one of them is an edge or
     * this holds none of it: half a rule held is a rule nobody holds.
     */
    private static <A> List<Edge<A>> edgesOf(AffineConstraint<A> constraint,
                                             CanonicalOrder<A> order) {
        List<Edge<A>> out = new ArrayList<>();
        for (AffineConstraint.HalfSpace<A> half : constraint.halfSpaces()) {
            Edge<A> edge = edgeOf(half.form(), half.bound(), order);
            if (edge == null) {
                return List.of();
            }
            out.add(edge);
        }
        return List.copyOf(out);
    }

    /**
     * Whether {@code half} is a bound on the difference of two positions: the shape a path of
     * differences runs along, and so the one a closure has something to compose it with.
     *
     * <p>A bound on one position is an edge too, and is not asked about here: it reaches the ends a
     * round carries along the differences, and holds nothing a path could pass through.
     */
    static <A> boolean relatesTwoPositions(AffineConstraint.HalfSpace<A> half,
                                           CanonicalOrder<A> order) {
        return edgeOf(half.form(), half.bound(), order) instanceof Edge.Between<A>;
    }

    /**
     * Whether {@code equality} is of the shape these hold exactly, as the two bounds it is: a
     * difference of two positions, or a bound on one. Asked of the same reading that makes the
     * edges, so what is held exactly and what is said to be held exactly cannot differ.
     */
    static <A> boolean holdsExactly(AffineConstraint.Equality<A> equality, CanonicalOrder<A> order) {
        return edgeOf(equality.form(), ExactCut.inclusive(equality.at()), order) != null;
    }

    /**
     * The edge one half-space is, or null where it is not of this shape.
     *
     * <p>Which two positions the difference is between is read off the weight at each and not off
     * where either of them comes, so nothing here turns on the walk. It is taken in the one order
     * the positions decide all the same: a walk of a form is where an order the form does not hold
     * gets into an answer, and the way to keep it out is to have no walk that could.
     */
    private static <A> Edge<A> edgeOf(CanonicalForm<A> form, ExactCut bound,
                                      CanonicalOrder<A> order) {
        List<Map.Entry<A, ExactRatio>> coefs = form.entriesIn(order);
        if (coefs.size() == 1) {
            Map.Entry<A, ExactRatio> only = coefs.getFirst();
            return only.getValue().signum() > 0
                    ? new Edge.Above<>(only.getKey(), bound)      // a - 0 <= w
                    : new Edge.Below<>(only.getKey(), bound);     // 0 - a <= w
        }
        if (coefs.size() != 2) {
            return null;
        }
        A up = null;
        A down = null;
        for (Map.Entry<A, ExactRatio> each : coefs) {
            if (each.getValue().equals(ExactRatio.ONE)) {
                up = each.getKey();
            } else if (each.getValue().equals(ExactRatio.ONE.negated())) {
                down = each.getKey();
            } else {
                return null;   // a sum, or a weighted difference, which is not of this shape
            }
        }
        return up == null || down == null ? null : new Edge.Between<>(up, down, bound);
    }

    /** One rule of this shape, as an edge: from a position to nought, from nought to a position, or
     *  between two positions. */
    private sealed interface Edge<A> {

        /** {@code position - 0 <= at}. */
        record Above<A>(A position, ExactCut at) implements Edge<A> {}

        /** {@code 0 - position <= at}. */
        record Below<A>(A position, ExactCut at) implements Edge<A> {}

        /** {@code from - to <= at}. */
        record Between<A>(A from, A to, ExactCut at) implements Edge<A> {}
    }

    /**
     * The edges closed over each other, and whether what is left holds anything.
     *
     * <p>Every path, because a bound on one position is reached through every other:
     * {@code a - b <= 0} with {@code b <= 1440} bounds {@code a} at 1440 though nothing was ever
     * said about {@code a} alone. A path reaches its far end only where every hop on it does, which
     * is why the strictness travels with the sum rather than being decided at the end.
     *
     * <p>The differences among the positions are closed first ({@link Paths}). A shortest path that
     * goes through nought goes through it once, so each bound is then the tightest of its own edge
     * and every closed difference followed by another position's edge, and a cycle through nought is
     * a position whose two bounds have crossed.
     */
    private static <A> DifferenceBounds<A> closing(Map<A, Map<A, ExactCut>> between,
                                                   Map<A, ExactCut> aboveEdges,
                                                   Map<A, ExactCut> belowEdges,
                                                   Set<A> positions) {
        Paths<A> paths = new Paths<>(positions);
        if (!paths.closed(between)) {
            return new DifferenceBounds<>(Map.of(), Map.of(), Map.of(), positions, true,
                    paths.everyHopWasComposed);
        }
        boolean everyHopWasComposed = paths.everyHopWasComposed;
        Map<A, Map<A, ExactCut>> shortest = paths.inTheOrderOf(positions);
        Map<A, ExactCut> above = new LinkedHashMap<>(aboveEdges);
        Map<A, ExactCut> below = new LinkedHashMap<>(belowEdges);
        for (Map.Entry<A, Map<A, ExactCut>> row : shortest.entrySet()) {
            A from = row.getKey();
            ExactCut leaving = belowEdges.get(from);
            for (Map.Entry<A, ExactCut> apart : row.getValue().entrySet()) {
                // `from - to <= d` with `to - 0 <= w` is `from - 0 <= d + w`.
                ExactCut onTo = aboveEdges.get(apart.getKey());
                if (onTo != null) {
                    ExactCut bound = composed(apart.getValue(), onTo);
                    if (bound == null) {
                        everyHopWasComposed = false;
                    } else {
                        above.merge(from, bound, ExactCut::tighterUpper);
                    }
                }
                // `0 - from <= w` with `from - to <= d` is `0 - to <= w + d`.
                if (leaving != null) {
                    ExactCut bound = composed(leaving, apart.getValue());
                    if (bound == null) {
                        everyHopWasComposed = false;
                    } else {
                        below.merge(apart.getKey(), bound, ExactCut::tighterUpper);
                    }
                }
            }
        }
        // A cycle is a difference of a node from itself, which is nought. One summing below nought
        // is a contradiction, and so is one summing to nought without reaching it. Through nought,
        // the cycle is a position's bound below and its bound above, and it comes back below where it
        // started exactly where the two have crossed — which is asked of the ends and not of a sum.
        boolean nothing = false;
        for (Map.Entry<A, Map<A, ExactCut>> row : shortest.entrySet()) {
            ExactCut cycle = row.getValue().get(row.getKey());
            if (cycle != null && (cycle.at().signum() < 0
                    || (cycle.at().isZero() && !cycle.inclusive()))) {
                nothing = true;
                break;
            }
        }
        if (!nothing) {
            for (A position : positions) {
                if (crossed(below.get(position), above.get(position))) {
                    nothing = true;
                    break;
                }
            }
        }
        return new DifferenceBounds<>(shortest, above, below, positions, nothing,
                everyHopWasComposed);
    }

    /**
     * The closed differences among positions, worked out by taking the positions out one at a time,
     * the one related to the fewest others first, and putting them back in the reverse order.
     *
     * <p>Taking a position out composes the hops into it with the hops out of it, and only among the
     * positions still in. What it saw of those when it went is its row and column of shortest paths
     * through the positions that went before it. Putting the positions back in the reverse order
     * finishes every path: the first position of a shortest path that went out later is where the
     * part through earlier ones stops, and what follows is already closed. A hop the exact
     * arithmetic cannot sum is one this does not compose, same as one that was never an edge: the
     * closure is looser than the true one by exactly this hop, which is sound for every reading that
     * asks whether something is left, and is why {@link #everyHopWasComposed} is carried rather than
     * thrown past.
     *
     * <p>A position related to few others costs few hops and leaves nothing behind for the ones
     * after it to be read against, so a chain of rules relating each position to the next costs the
     * square of its length in the paths it ends with, where closing through every position in turn
     * costs the cube.
     */
    private static final class Paths<A> {

        /** A position taken out, and the shortest paths to and from the positions still in. */
        private record Taken<A>(A position, Map<A, ExactCut> to, Map<A, ExactCut> from) {}

        private final Set<A> positions;
        private final Map<A, Map<A, ExactCut>> shortest = new LinkedHashMap<>();
        private boolean everyHopWasComposed = true;

        Paths(Set<A> positions) {
            this.positions = positions;
            positions.forEach(position -> shortest.put(position, new LinkedHashMap<>()));
        }

        /** Closes {@code between}, and says whether anything is left: not where a cycle sums below
         *  nought. */
        boolean closed(Map<A, Map<A, ExactCut>> between) {
            Map<A, Map<A, ExactCut>> out = new LinkedHashMap<>();
            Map<A, Map<A, ExactCut>> into = new LinkedHashMap<>();
            for (A position : positions) {
                out.put(position, new LinkedHashMap<>());
                into.put(position, new LinkedHashMap<>());
            }
            between.forEach((from, row) -> row.forEach((to, by) -> {
                out.get(from).put(to, by);
                into.get(to).put(from, by);
            }));
            Deque<Taken<A>> taken = new ArrayDeque<>();
            Set<A> left = new LinkedHashSet<>(positions);
            while (!left.isEmpty()) {
                A position = relatedToTheFewest(left, out, into);
                left.remove(position);
                Map<A, ExactCut> to = out.remove(position);
                Map<A, ExactCut> from = into.remove(position);
                to.remove(position);
                from.remove(position);
                from.keySet().forEach(each -> out.get(each).remove(position));
                to.keySet().forEach(each -> into.get(each).remove(position));
                for (Map.Entry<A, ExactCut> hopIn : from.entrySet()) {
                    for (Map.Entry<A, ExactCut> hopOut : to.entrySet()) {
                        ExactCut round = composed(hopIn.getValue(), hopOut.getValue());
                        if (round == null) {
                            everyHopWasComposed = false;
                        } else if (hopIn.getKey().equals(hopOut.getKey())
                                && (round.at().signum() < 0
                                        || (round.at().isZero() && !round.inclusive()))) {
                            return false;
                        } else if (ExactCut.tighterUpper(
                                out.get(hopIn.getKey()).get(hopOut.getKey()), round) == round) {
                            out.get(hopIn.getKey()).put(hopOut.getKey(), round);
                            into.get(hopOut.getKey()).put(hopIn.getKey(), round);
                        }
                    }
                }
                taken.push(new Taken<>(position, to, from));
            }
            Set<A> back = new LinkedHashSet<>();
            while (!taken.isEmpty()) {
                Taken<A> each = taken.pop();
                A position = each.position();
                for (Map.Entry<A, ExactCut> hop : each.to().entrySet()) {
                    keep(position, hop.getKey(), hop.getValue());
                    for (Map.Entry<A, ExactCut> onwards
                            : shortest.get(hop.getKey()).entrySet()) {
                        keepComposed(position, onwards.getKey(), hop.getValue(),
                                onwards.getValue());
                    }
                }
                for (Map.Entry<A, ExactCut> hop : each.from().entrySet()) {
                    keep(hop.getKey(), position, hop.getValue());
                    for (A before : back) {
                        ExactCut reaching = shortest.get(before).get(hop.getKey());
                        if (reaching != null) {
                            keepComposed(before, position, reaching, hop.getValue());
                        }
                    }
                }
                back.add(position);
            }
            return true;
        }

        /** The position of {@code left} with the fewest paths through it to compose. */
        private A relatedToTheFewest(Set<A> left, Map<A, Map<A, ExactCut>> out,
                                     Map<A, Map<A, ExactCut>> into) {
            A fewest = null;
            long cost = Long.MAX_VALUE;
            for (A position : left) {
                long hops = (long) (into.get(position).size()
                        - (into.get(position).containsKey(position) ? 1 : 0))
                        * (out.get(position).size()
                        - (out.get(position).containsKey(position) ? 1 : 0));
                if (hops < cost) {
                    fewest = position;
                    cost = hops;
                }
            }
            return fewest;
        }

        private void keepComposed(A from, A to, ExactCut first, ExactCut second) {
            ExactCut round = composed(first, second);
            if (round == null) {
                everyHopWasComposed = false;
            } else {
                keep(from, to, round);
            }
        }

        private void keep(A from, A to, ExactCut by) {
            if (ExactCut.tighterUpper(shortest.get(from).get(to), by) == by) {
                shortest.get(from).put(to, by);
            }
        }

        /** The rows that say anything, each in the order {@code order} puts its positions in, so
         *  that what the closure holds does not depend on the order positions were taken out. */
        Map<A, Map<A, ExactCut>> inTheOrderOf(Set<A> order) {
            Map<A, Map<A, ExactCut>> ordered = new LinkedHashMap<>();
            for (A from : order) {
                Map<A, ExactCut> row = shortest.get(from);
                if (row.isEmpty()) {
                    continue;
                }
                Map<A, ExactCut> inOrder = new LinkedHashMap<>();
                for (A to : order) {
                    ExactCut by = row.get(to);
                    if (by != null) {
                        inOrder.put(to, by);
                    }
                }
                ordered.put(from, inOrder);
            }
            return ordered;
        }
    }

    /** Whether {@code 0 - a <= least} and {@code a - 0 <= most} leave {@code a} no value. */
    private static boolean crossed(ExactCut least, ExactCut most) {
        if (least == null || most == null) {
            return false;
        }
        int order = least.at().negated().compareTo(most.at());
        return order > 0 || (order == 0 && !(least.inclusive() && most.inclusive()));
    }

    /** {@code a} then {@code b}, or null where the exact arithmetic cannot hold the sum. Counted, for
     *  a test that asks how many hops the closure composed. */
    private static ExactCut composed(ExactCut a, ExactCut b) {
        long[] counting = COUNTING_HOPS;
        if (counting != null) {
            counting[0]++;
        }
        return ExactCut.meetingBoth(a, b) instanceof ExactAnswer.Held<ExactCut> held
                ? held.value() : null;
    }

    /** Where a test in this package counts the hops the closure composes, and null everywhere else.
     *  What the closure comes to says nothing about how many hops it composed to get there, so a
     *  closure that relates every two positions and one that relates only those the rules relate
     *  answer alike, and what separates them has nowhere else to be read. */
    static long[] COUNTING_HOPS;

    /**
     * Whether nothing at all satisfies what this holds.
     *
     * <p>Complete for this fragment: a difference-bound system has no solution exactly where closing
     * it produces a cycle below nought, so this is not merely a proof of emptiness but a decision of
     * it — over what this holds, and no further.
     */
    public boolean holdsNothing() {
        return holdsNothing;
    }

    /**
     * Whether every hop the closure tried to sum was one the exact arithmetic could hold.
     *
     * <p>A model's own numbers can put two run ends far enough apart in scale that their sum has no
     * representation this host writes ({@link ExactCut#meetingBoth}). Where that happens the closure
     * still closes — a hop it could not sum is one it treats as absent, which only ever widens what
     * is left — but it is then no longer complete for this fragment, and a reader depending on
     * completeness ({@link souther.compiler.numeric.ProjectionCertificate}) has to be told rather
     * than shown a closure that looks whole.
     */
    public boolean everyHopWasComposed() {
        return everyHopWasComposed;
    }

    /** The tightest {@code atom <= …} this proves, or {@code null} where it proves none. */
    public ExactCut upperBoundOf(A atom) {
        return whereThereAreValues(above.get(atom));
    }

    /**
     * The tightest {@code atom >= …} this proves, or {@code null} where it proves none.
     *
     * <p>An edge the other way says {@code 0 - a <= w}, which is {@code a >= -w} — the same cut on
     * the other side of nought, keeping whether the value itself is reached.
     */
    public ExactCut lowerBoundOf(A atom) {
        ExactCut under = whereThereAreValues(below.get(atom));
        return under == null ? null : new ExactCut(under.at().negated(), under.inclusive());
    }

    /**
     * The tightest {@code a - b <= …} this proves, or {@code null} where it proves none.
     *
     * <p>The tighter of the two routes there are: along the differences, and through nought, which
     * is {@code a}'s bound above less {@code b}'s bound below. Where those two bounds are too far
     * apart in scale for the exact arithmetic to sum, the route through nought bounds nothing — the
     * same as a hop the closure cannot sum, and looser than the true answer by that route.
     */
    public ExactCut differenceBound(A a, A b) {
        if (a.equals(b)) {
            return whereThereAreValues(ExactCut.inclusive(ExactRatio.ZERO));
        }
        Map<A, ExactCut> row = related.get(a);
        ExactCut along = row == null ? null : row.get(b);
        ExactCut most = above.get(a);
        ExactCut least = below.get(b);
        ExactCut throughNought = most == null || least == null ? null
                : ExactCut.meetingBoth(most, least).orNull();
        return whereThereAreValues(ExactCut.tighterUpper(along, throughNought));
    }

    /**
     * Whether {@link #differenceBound} of {@code a - b} is the tightest this proves. It is not where
     * both positions are bounded and their bounds cannot be summed: the route through nought is then
     * left out, and what comes back is looser than the paths say, or nothing where nothing else
     * relates them — which is not that nothing bounds the difference.
     *
     * <p>{@link #everyHopWasComposed} says as much of the closure, and this of one question put to
     * it, which sums the two bounds when it is asked and not before.
     */
    public boolean differenceBoundWasComposed(A a, A b) {
        ExactCut most = above.get(a);
        ExactCut least = below.get(b);
        return a.equals(b) || most == null || least == null
                || ExactCut.meetingBoth(most, least) instanceof ExactAnswer.Held<ExactCut>;
    }

    /**
     * Every difference closed along the rules relating two positions, without going through nought.
     *
     * <p>What carries a bound on one position onto another. A difference through nought is the two
     * positions' own bounds, so it carries onto a position nothing a box already inside those bounds
     * does not hold there; what is left are these, and there are as many as the rules relate.
     */
    public List<Apart<A>> relations() {
        if (holdsNothing) {
            throw new IllegalStateException(
                    "nothing is left, so no difference is the tightest; ask holdsNothing first");
        }
        return relations;
    }

    /**
     * The answer, where there is one to give.
     *
     * <p>Where nothing is left there is no tightest bound: every bound holds, and closing a system
     * that comes back below where it started walks the cycle as many times as the closure happened
     * to reach it — so what these would hand back is a number that moves with the order the rules
     * arrived in, which is the one thing this whole arrangement is for.
     *
     * <p>Refused rather than answered with no bound. No bound reads as "unbounded that way", which
     * is the opposite of the truth here and the dangerous direction: a caller taking it would go
     * looking for rows in a value nobody can build. Whether anything is left is
     * {@link #holdsNothing}, and it is the question to ask first.
     */
    private ExactCut whereThereAreValues(ExactCut answer) {
        if (holdsNothing) {
            throw new IllegalStateException(
                    "nothing is left, so no bound is the tightest; ask holdsNothing first");
        }
        return answer;
    }

    /** Every position this says anything about. */
    public Set<A> positions() {
        return new LinkedHashSet<>(positions);
    }
}
