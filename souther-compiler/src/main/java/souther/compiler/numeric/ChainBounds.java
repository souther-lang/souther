package souther.compiler.numeric;

import java.math.BigInteger;
import java.util.List;
import java.util.Map;

/**
 * The closure of bounds on coordinates {@code 0 .. n-1} and on the differences of neighbouring
 * coordinates, held as the rules state them and answered by walking the chain.
 *
 * <p>Where every rule bounds one coordinate or the difference of two neighbours, a path from one
 * coordinate to another has one route and the closure of all the differences is the sum of the
 * hops along it. So no table of every pair is made: the bound each coordinate comes to is the
 * tightest of its own and of every other coordinate's carried along the chain, which two passes
 * over the chain give, and a difference is summed along the chain when it is asked. That is the
 * answer {@link DifferenceBounds} gives for the same rules, which is what a test holds it to, at a
 * cost that grows with the chain and not with its square.
 *
 * <p>Where a rule bounds the difference of two coordinates that are not neighbours there is more
 * than one route, and {@link #over} has no answer: those rules are closed by
 * {@link DifferenceBounds}.
 */
final class ChainBounds implements PrefixBasis.Closed {

    private static final CanonicalOrder<Integer> BY_COORDINATE = Integer::compare;

    /**
     * What a bound may come to for the closure to be made here: a whole number of no more than a
     * thousand bits, either way — every {@code Int} there is, with its ends, and a great deal more.
     *
     * <p>That is what makes the closure complete without the sums being tried. A path of the chain
     * is a sum of its hops, and the sum of fewer than a billion bounds of this size is a whole
     * number of under a thousand and thirty bits, which the exact arithmetic holds: what it cannot
     * hold is a sum whose digits are as many as two exponents near the end of the scale range are
     * apart. So no sum {@link DifferenceBounds} would try is one it cannot hold, and the closure of
     * the differences of a chain is complete — {@link #everyHopWasComposed} says what that closure
     * says — whichever pairs the questions asked of it reach. A bound near the end of what the
     * arithmetic holds is one a sum of two may not be held for, which a closure of every pair finds
     * and this does not look for: those rules are left to {@link DifferenceBounds}.
     */
    private static final ExactRatio LARGEST = ExactRatio.of(BigInteger.ONE.shiftLeft(1000));

    private static boolean withinTheRange(ExactCut bound) {
        return bound.at().isWhole() && bound.at().compareTo(LARGEST) <= 0
                && bound.at().negated().compareTo(LARGEST) <= 0;
    }

    private final int size;
    private final ExactCut[] above;
    private final ExactCut[] below;
    private final ExactCut[] forward;
    private final ExactCut[] backward;
    private final boolean holdsNothing;
    private final boolean everyHopWasComposed;

    private ChainBounds(int size, ExactCut[] aboveEdge, ExactCut[] belowEdge, ExactCut[] forward,
                        ExactCut[] backward) {
        this.size = size;
        this.forward = forward;
        this.backward = backward;
        boolean composed = true;
        boolean nothing = false;
        for (int at = 0; at + 1 < size; at++) {
            if (forward[at] != null && backward[at] != null) {
                ExactCut round = composed(forward[at], backward[at]);
                if (round == null) {
                    composed = false;
                } else if (round.at().signum() < 0 || (round.at().isZero() && !round.inclusive())) {
                    nothing = true;
                }
            }
        }
        ExactCut[] fromBelow = new ExactCut[size];
        ExactCut[] fromAbove = new ExactCut[size];
        ExactCut[] top = new ExactCut[size];
        ExactCut[] bottom = new ExactCut[size];
        // A bound on x_i carried up the chain, and down it.
        for (int at = 0; at < size; at++) {
            fromBelow[at] = aboveEdge[at];
            if (at > 0 && backward[at - 1] != null && fromBelow[at - 1] != null) {
                ExactCut carried = composed(backward[at - 1], fromBelow[at - 1]);
                if (carried == null) {
                    composed = false;
                } else {
                    fromBelow[at] = ExactCut.tighterUpper(fromBelow[at], carried);
                }
            }
        }
        for (int at = size - 1; at >= 0; at--) {
            fromAbove[at] = aboveEdge[at];
            if (at + 1 < size && forward[at] != null && fromAbove[at + 1] != null) {
                ExactCut carried = composed(forward[at], fromAbove[at + 1]);
                if (carried == null) {
                    composed = false;
                } else {
                    fromAbove[at] = ExactCut.tighterUpper(fromAbove[at], carried);
                }
            }
            top[at] = ExactCut.tighterUpper(fromAbove[at], fromBelow[at]);
        }
        // A bound on 0 - x_i carried the same two ways.
        for (int at = 0; at < size; at++) {
            fromBelow[at] = belowEdge[at];
            if (at > 0 && forward[at - 1] != null && fromBelow[at - 1] != null) {
                ExactCut carried = composed(fromBelow[at - 1], forward[at - 1]);
                if (carried == null) {
                    composed = false;
                } else {
                    fromBelow[at] = ExactCut.tighterUpper(fromBelow[at], carried);
                }
            }
        }
        for (int at = size - 1; at >= 0; at--) {
            fromAbove[at] = belowEdge[at];
            if (at + 1 < size && backward[at] != null && fromAbove[at + 1] != null) {
                ExactCut carried = composed(fromAbove[at + 1], backward[at]);
                if (carried == null) {
                    composed = false;
                } else {
                    fromAbove[at] = ExactCut.tighterUpper(fromAbove[at], carried);
                }
            }
            bottom[at] = ExactCut.tighterUpper(fromAbove[at], fromBelow[at]);
        }
        if (!nothing) {
            for (int at = 0; at < size; at++) {
                if (crossed(bottom[at], top[at])) {
                    nothing = true;
                    break;
                }
            }
        }
        this.above = top;
        this.below = bottom;
        this.holdsNothing = nothing;
        this.everyHopWasComposed = composed;
    }

    /**
     * The closure of {@code moved}, or null where a rule is not a bound on one coordinate or on
     * the difference of two neighbours.
     */
    static ChainBounds over(List<AffineConstraint<Integer>> moved) {
        int size = 0;
        for (AffineConstraint<Integer> rule : moved) {
            if (!(rule instanceof AffineConstraint.HalfSpace<Integer> half)
                    || !withinTheRange(half.bound())) {
                return null;
            }
            for (Map.Entry<Integer, ExactRatio> each : half.form().entriesIn(BY_COORDINATE)) {
                size = Math.max(size, each.getKey() + 1);
            }
        }
        ExactCut[] aboveEdge = new ExactCut[size];
        ExactCut[] belowEdge = new ExactCut[size];
        ExactCut[] forward = new ExactCut[size];
        ExactCut[] backward = new ExactCut[size];
        for (AffineConstraint<Integer> rule : moved) {
            AffineConstraint.HalfSpace<Integer> half = (AffineConstraint.HalfSpace<Integer>) rule;
            List<Map.Entry<Integer, ExactRatio>> coefs = half.form().entriesIn(BY_COORDINATE);
            if (coefs.size() == 1) {
                Map.Entry<Integer, ExactRatio> only = coefs.getFirst();
                int at = only.getKey();
                if (only.getValue().signum() > 0) {
                    aboveEdge[at] = ExactCut.tighterUpper(aboveEdge[at], half.bound());
                } else {
                    belowEdge[at] = ExactCut.tighterUpper(belowEdge[at], half.bound());
                }
            } else if (coefs.size() == 2) {
                Integer up = null;
                Integer down = null;
                for (Map.Entry<Integer, ExactRatio> each : coefs) {
                    if (each.getValue().equals(ExactRatio.ONE)) {
                        up = each.getKey();
                    } else if (each.getValue().equals(ExactRatio.ONE.negated())) {
                        down = each.getKey();
                    } else {
                        return null;
                    }
                }
                if (up == null || down == null || Math.abs(up - down) != 1) {
                    return null;
                }
                if (up < down) {
                    forward[up] = ExactCut.tighterUpper(forward[up], half.bound());
                } else {
                    backward[down] = ExactCut.tighterUpper(backward[down], half.bound());
                }
            } else {
                return null;
            }
        }
        return new ChainBounds(size, aboveEdge, belowEdge, forward, backward);
    }

    @Override
    public boolean holdsNothing() {
        return holdsNothing;
    }

    @Override
    public boolean everyHopWasComposed() {
        return everyHopWasComposed;
    }

    @Override
    public ExactCut upperBoundOf(int at) {
        return whereThereAreValues(at < size ? above[at] : null);
    }

    @Override
    public ExactCut lowerBoundOf(int at) {
        ExactCut under = whereThereAreValues(at < size ? below[at] : null);
        return under == null ? null : new ExactCut(under.at().negated(), under.inclusive());
    }

    @Override
    public ExactCut differenceBound(int a, int b) {
        if (a == b) {
            return whereThereAreValues(ExactCut.inclusive(ExactRatio.ZERO));
        }
        if (holdsNothing) {
            whereThereAreValues(null);
        }
        ExactCut along = along(a, b);
        ExactCut most = a < size ? above[a] : null;
        ExactCut least = b < size ? below[b] : null;
        ExactCut throughNought = most == null || least == null ? null
                : ExactCut.meetingBoth(most, least).orNull();
        return ExactCut.tighterUpper(along, throughNought);
    }

    @Override
    public boolean differenceBoundWasComposed(int a, int b) {
        if (a == b) {
            return true;
        }
        if (!alongWasComposed(a, b)) {
            return false;
        }
        ExactCut most = a < size ? above[a] : null;
        ExactCut least = b < size ? below[b] : null;
        return most == null || least == null
                || ExactCut.meetingBoth(most, least) instanceof ExactAnswer.Held<ExactCut>;
    }

    /** The sum of the hops from {@code a} to {@code b} along the chain, or null where one is
     *  missing or the sum cannot be held. */
    private ExactCut along(int a, int b) {
        if (a >= size || b >= size) {
            return null;
        }
        ExactCut sum = null;
        int step = a < b ? 1 : -1;
        for (int at = a; at != b; at += step) {
            ExactCut hop = step > 0 ? forward[at] : backward[at - 1];
            if (hop == null) {
                return null;
            }
            if (sum == null) {
                sum = hop;
            } else {
                sum = composed(sum, hop);
                if (sum == null) {
                    return null;
                }
            }
        }
        return sum;
    }

    /** Whether every sum {@link #along} comes to was one the exact arithmetic could hold. */
    private boolean alongWasComposed(int a, int b) {
        if (a >= size || b >= size) {
            return true;
        }
        ExactCut sum = null;
        int step = a < b ? 1 : -1;
        for (int at = a; at != b; at += step) {
            ExactCut hop = step > 0 ? forward[at] : backward[at - 1];
            if (hop == null) {
                return true;
            }
            sum = sum == null ? hop : composed(sum, hop);
            if (sum == null) {
                return false;
            }
        }
        return true;
    }

    private ExactCut whereThereAreValues(ExactCut answer) {
        if (holdsNothing) {
            throw new IllegalStateException(
                    "nothing is left, so no bound is the tightest; ask holdsNothing first");
        }
        return answer;
    }

    private static boolean crossed(ExactCut least, ExactCut most) {
        if (least == null || most == null) {
            return false;
        }
        int order = least.at().negated().compareTo(most.at());
        return order > 0 || (order == 0 && !(least.inclusive() && most.inclusive()));
    }

    private static ExactCut composed(ExactCut a, ExactCut b) {
        return ExactCut.meetingBoth(a, b) instanceof ExactAnswer.Held<ExactCut> held
                ? held.value() : null;
    }
}
