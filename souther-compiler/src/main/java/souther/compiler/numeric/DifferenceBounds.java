package souther.compiler.numeric;

import java.util.ArrayList;
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
 * <p><b>Complete for what it holds.</b> Closing a difference-bound system finds a negative cycle
 * exactly when one exists, so within this fragment "the rules leave nothing" and "this says the
 * rules leave nothing" are the same statement. That is not true of the algebra as a whole — a
 * general sum is held elsewhere and reasoned about approximately — so what holds overall is one
 * direction only: where this says nothing is left, nothing is.
 *
 * <p>Exact throughout. The edges are {@link Rational}, and a bound only becomes a decimal somebody
 * can read at the edge where it is handed over. Closed on decimals rounded to a fixed number of
 * digits, a system with no solution comes back with one — the arithmetic that separates the two ends
 * of {@code 3a = 1} is finer than the rounding.
 */
public final class DifferenceBounds<A> {

    /** One end of an edge: a position, or the nought every bound is a difference from. */
    public sealed interface Node<A> {

        record OfAPosition<A>(A atom) implements Node<A> {
            public OfAPosition {
                if (atom == null) {
                    throw new IllegalArgumentException("a position has a name");
                }
            }

            @Override
            public String toString() {
                return String.valueOf(atom);
            }
        }

        /** Nought, which is what a bound on one position is a difference from. */
        record Nought<A>() implements Node<A> {
            @Override
            public String toString() {
                return "0";
            }
        }
    }

    private final Map<Node<A>, Map<Node<A>, RationalCut>> closed;
    private final boolean holdsNothing;

    private DifferenceBounds(Map<Node<A>, Map<Node<A>, RationalCut>> closed, boolean holdsNothing) {
        this.closed = closed;
        this.holdsNothing = holdsNothing;
    }

    /**
     * The constraints of this shape among {@code constraints}, closed over each other.
     *
     * <p>Everything else is left where it is, and nothing has to sort the rules first: what is not
     * of this shape is skipped here and read by the reduction, and a rule of this shape is read by
     * both — exactly, here, and again as a plain sum there, which costs a little and says nothing
     * new. So there is one decision about the shape and it is made here.
     */
    public static <A> DifferenceBounds<A> over(Iterable<AffineConstraint<A>> constraints) {
        Map<Node<A>, Map<Node<A>, RationalCut>> edges = new LinkedHashMap<>();
        for (AffineConstraint<A> each : constraints) {
            for (Edge<A> edge : edgesOf(each)) {
                edges.computeIfAbsent(edge.from(), k -> new LinkedHashMap<>())
                        .merge(edge.to(), edge.at(), RationalCut::tighterUpper);
            }
        }
        return closing(edges);
    }

    /** Whether this can hold what {@code constraint} says, in full — which is what the shapes above
     *  amount to, asked directly so that they can be pinned down. */
    static <A> boolean canHold(AffineConstraint<A> constraint) {
        return !edgesOf(constraint).isEmpty();
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
     */
    private static <A> List<Edge<A>> edgesOf(AffineConstraint<A> constraint) {
        return switch (constraint) {
            case AffineConstraint.HalfSpace<A> half -> {
                Edge<A> edge = edgeOf(half.form(), half.bound());
                yield edge == null ? List.of() : List.of(edge);
            }
            // Held at a value is held no higher and no lower, and both are of this shape wherever
            // one of them is.
            case AffineConstraint.Equality<A> at -> {
                Edge<A> up = edgeOf(at.form(), RationalCut.inclusive(at.at()));
                Edge<A> down = edgeOf(at.form().negated(),
                        RationalCut.inclusive(at.at().negated()));
                yield up == null || down == null ? List.of() : List.of(up, down);
            }
            // A hole is not a bound, and which side of it anything lies is not this one's to say.
            case AffineConstraint.Disequality<A> hole -> List.of();
        };
    }

    private static <A> Edge<A> edgeOf(CanonicalForm<A> form, RationalCut bound) {
        Map<A, Rational> coefs = form.coefs();
        if (coefs.size() == 1) {
            Map.Entry<A, Rational> only = coefs.entrySet().iterator().next();
            Node<A> position = new Node.OfAPosition<>(only.getKey());
            Node<A> nought = new Node.Nought<A>();
            return only.getValue().signum() > 0
                    ? new Edge<>(position, nought, bound)      // a - 0 <= w
                    : new Edge<>(nought, position, bound);     // 0 - a <= w
        }
        if (coefs.size() != 2) {
            return null;
        }
        A up = null;
        A down = null;
        for (Map.Entry<A, Rational> each : coefs.entrySet()) {
            if (each.getValue().equals(Rational.ONE)) {
                up = each.getKey();
            } else if (each.getValue().equals(Rational.ONE.negated())) {
                down = each.getKey();
            } else {
                return null;   // a sum, or a weighted difference, which is not of this shape
            }
        }
        return up == null || down == null ? null
                : new Edge<>(new Node.OfAPosition<>(up), new Node.OfAPosition<>(down), bound);
    }

    /** {@code from - to <= at}. */
    private record Edge<A>(Node<A> from, Node<A> to, RationalCut at) {}

    /**
     * The edges closed over each other, and whether what is left holds anything.
     *
     * <p>Every path, because a bound on one position is reached through every other:
     * {@code a - b <= 0} with {@code b <= 1440} bounds {@code a} at 1440 though nothing was ever
     * said about {@code a} alone. A path reaches its far end only where every hop on it does, which
     * is why the strictness travels with the sum rather than being decided at the end.
     */
    private static <A> DifferenceBounds<A> closing(Map<Node<A>, Map<Node<A>, RationalCut>> edges) {
        Set<Node<A>> nodes = new LinkedHashSet<>(edges.keySet());
        edges.values().forEach(row -> nodes.addAll(row.keySet()));
        Map<Node<A>, Map<Node<A>, RationalCut>> shortest = new LinkedHashMap<>();
        edges.forEach((from, row) -> shortest.put(from, new LinkedHashMap<>(row)));
        for (Node<A> through : nodes) {
            Map<Node<A>, RationalCut> onwards = shortest.get(through);
            if (onwards == null) {
                continue;
            }
            List<Map.Entry<Node<A>, RationalCut>> hops = List.copyOf(onwards.entrySet());
            for (Node<A> from : nodes) {
                if (from.equals(through)) {
                    continue;
                }
                RationalCut reaching = at(shortest, from, through);
                if (reaching == null) {
                    continue;
                }
                for (Map.Entry<Node<A>, RationalCut> hop : hops) {
                    RationalCut round = RationalCut.meetingBoth(reaching, hop.getValue());
                    RationalCut known = at(shortest, from, hop.getKey());
                    if (RationalCut.tighterUpper(known, round) == round) {
                        shortest.computeIfAbsent(from, k -> new LinkedHashMap<>())
                                .put(hop.getKey(), round);
                    }
                }
            }
        }
        // A cycle is a difference of a node from itself, which is nought. One summing below nought
        // is a contradiction, and so is one summing to nought without reaching it.
        boolean nothing = false;
        for (Node<A> node : nodes) {
            RationalCut cycle = at(shortest, node, node);
            if (cycle != null && (cycle.at().signum() < 0
                    || (cycle.at().isZero() && !cycle.inclusive()))) {
                nothing = true;
                break;
            }
        }
        return new DifferenceBounds<>(shortest, nothing);
    }

    private static <A> RationalCut at(Map<Node<A>, Map<Node<A>, RationalCut>> table,
                                      Node<A> from, Node<A> to) {
        Map<Node<A>, RationalCut> row = table.get(from);
        return row == null ? null : row.get(to);
    }

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

    /** The tightest {@code atom <= …} this proves, or {@code null} where it proves none. */
    public RationalCut upperBoundOf(A atom) {
        return whereThereAreValues(at(closed, new Node.OfAPosition<>(atom), new Node.Nought<A>()));
    }

    /**
     * The tightest {@code atom >= …} this proves, or {@code null} where it proves none.
     *
     * <p>An edge the other way says {@code 0 - a <= w}, which is {@code a >= -w} — the same cut on
     * the other side of nought, keeping whether the value itself is reached.
     */
    public RationalCut lowerBoundOf(A atom) {
        RationalCut below =
                whereThereAreValues(at(closed, new Node.Nought<A>(), new Node.OfAPosition<>(atom)));
        return below == null ? null : new RationalCut(below.at().negated(), below.inclusive());
    }

    /** The tightest {@code a - b <= …} this proves, or {@code null} where it proves none. */
    public RationalCut differenceBound(A a, A b) {
        if (a.equals(b)) {
            return whereThereAreValues(RationalCut.inclusive(Rational.ZERO));
        }
        return whereThereAreValues(
                at(closed, new Node.OfAPosition<>(a), new Node.OfAPosition<>(b)));
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
    private RationalCut whereThereAreValues(RationalCut answer) {
        if (holdsNothing) {
            throw new IllegalStateException(
                    "nothing is left, so no bound is the tightest; ask holdsNothing first");
        }
        return answer;
    }

    /** Every position this says anything about. */
    public Set<A> positions() {
        Set<A> out = new LinkedHashSet<>();
        List<Node<A>> reached = new ArrayList<>(closed.keySet());
        closed.values().forEach(row -> reached.addAll(row.keySet()));
        for (Node<A> node : reached) {
            if (node instanceof Node.OfAPosition<A> at) {
                out.add(at.atom());
            }
        }
        return out;
    }
}
