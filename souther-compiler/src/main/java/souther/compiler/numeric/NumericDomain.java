package souther.compiler.numeric;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * A small numeric abstract domain — a per-atom interval plus difference-bound constraints
 * ({@code a - b <= c}, the octagon-style relational part) — over named atoms. An atom is the
 * numeric content of a variable, a field chain, or a newtype's wrapped value; what names one is the
 * caller's, and {@code Terms} in the checker is where the names come from today. Constants are
 * {@link BigDecimal}; {@code null} bounds are ±infinity.
 *
 * <p>{@link #assume} tightens the domain along a {@code guard}/{@code if} guard or an input
 * newtype's invariant, and {@link #entails} / {@link #refutes} answer whether a construction's
 * invariant is discharged or is definitely violated on the current path — which is the
 * invariant-discharge check, the caller this was written for. What it derives is bounded to
 * interval + difference-bound; a form of neither shape is kept as it was written, so a guard
 * restating an invariant still discharges it even where nothing can be derived from the two
 * together (spec §invariant-discharge). Instances are immutable — each operation returns a fresh
 * domain, threaded functionally like {@code TotalityChecker}'s scope map.
 */
public final class NumericDomain {

    /** A comparison of a {@link LinearForm} against zero. */
    public enum Rel { GE, GT, LE, LT, EQ, NE }

    /** An affine form {@code const + Σ coef·atom} over the domain's atoms. */
    public record LinearForm(BigDecimal constant, Map<String, BigDecimal> coefs) {
        public static LinearForm constant(BigDecimal c) {
            return new LinearForm(c, Map.of());
        }

        public static LinearForm atom(String a) {
            return new LinearForm(BigDecimal.ZERO, Map.of(a, BigDecimal.ONE));
        }

        public LinearForm plus(LinearForm o) {
            Map<String, BigDecimal> m = new HashMap<>(coefs);
            o.coefs.forEach((k, v) -> m.merge(k, v, BigDecimal::add));
            m.values().removeIf(v -> v.signum() == 0);
            return new LinearForm(constant.add(o.constant), m);
        }

        public LinearForm negate() {
            Map<String, BigDecimal> m = new HashMap<>();
            coefs.forEach((k, v) -> m.put(k, v.negate()));
            return new LinearForm(constant.negate(), m);
        }

        public LinearForm minus(LinearForm o) {
            return plus(o.negate());
        }

        /** This form scaled by a constant {@code k} (a scalar multiply). */
        public LinearForm times(BigDecimal k) {
            if (k.signum() == 0) {
                return constant(BigDecimal.ZERO);
            }
            Map<String, BigDecimal> m = new HashMap<>();
            coefs.forEach((key, v) -> m.put(key, v.multiply(k)));
            return new LinearForm(constant.multiply(k), m);
        }
    }

    /** A form asserted {@code f <= 0} (or {@code f < 0}) and kept as written, because its shape is
     * neither an interval nor a difference. */
    private record Asserted(LinearForm f, boolean strict) {}

    private final boolean bottom;                              // an infeasible path (guards contradict)
    private final Map<String, BigDecimal> lo;                  // atom -> lower bound (null key absent = -inf)
    private final Map<String, BigDecimal> hi;                  // atom -> upper bound (absent = +inf)
    private final Map<String, Map<String, BigDecimal>> diff;   // diff[a][b] = tightest known (a - b)
    private final List<Asserted> kept;                         // forms outside both shapes, as written
    private Map<String, Map<String, BigDecimal>> closed;       // diff closed transitively, on first ask

    private NumericDomain(boolean bottom, Map<String, BigDecimal> lo, Map<String, BigDecimal> hi,
                          Map<String, Map<String, BigDecimal>> diff, List<Asserted> kept) {
        this.bottom = bottom;
        this.lo = lo;
        this.hi = hi;
        this.diff = diff;
        this.kept = kept;
    }

    public static NumericDomain top() {
        return new NumericDomain(false, Map.of(), Map.of(), Map.of(), List.of());
    }

    public boolean isBottom() {
        return bottom;
    }

    // --- assume: tighten along `f rel 0` -------------------------------------------------------

    /** The domain refined by asserting {@code f rel 0}. */
    public NumericDomain assume(LinearForm f, Rel rel) {
        if (bottom || rel == Rel.NE) {
            // `f != 0` is a disjunction, and the domain holds conjunctions of bounds. Nothing to
            // record; what settles such a guard is the fact keyed on the comparison itself.
            return this;
        }
        if (rel == Rel.EQ) {
            return addLe(f, false).addLe(f.negate(), false);
        }
        // Reduce `f rel 0` to `g <= 0` (or `g < 0`): negate the form for >=/>, keep it for <=/<.
        return addLe(negOf(rel) ? f.negate() : f, strictOf(rel));
    }

    /** Assert {@code g <= 0} (or {@code g < 0} when strict), updating an interval or a difference, or
     * keeping the form as written when it is neither. Strictness only sharpens the constant case; for
     * an interval or difference a strict {@code < 0} is recorded as {@code <= 0} (weaker, so still
     * sound). */
    private NumericDomain addLe(LinearForm g, boolean strict) {
        Map<String, BigDecimal> c = g.coefs();
        if (c.isEmpty()) {
            boolean ok = strict ? g.constant().signum() < 0 : g.constant().signum() <= 0;
            return ok ? this : bottom();
        }
        if (c.size() == 1) {
            Map.Entry<String, BigDecimal> e = c.entrySet().iterator().next();
            String a = e.getKey();
            BigDecimal k = e.getValue();
            // k·a + const <= 0  =>  a <= -const/k (k>0, an upper bound)  or  a >= -const/k (k<0, a
            // lower bound). Round an inexact quotient conservatively — toward +inf for an upper bound,
            // toward -inf for a lower bound — so the recorded bound is never tighter than the true one.
            // A tighter-than-true bound would make entails/refutes unsound (a false E2010).
            boolean upper = k.signum() > 0;
            java.math.MathContext mc = new java.math.MathContext(
                    34, upper ? java.math.RoundingMode.CEILING : java.math.RoundingMode.FLOOR);
            BigDecimal bound = g.constant().negate().divide(k, mc);
            return upper ? withHi(a, bound) : withLo(a, bound);
        }
        String[] ab = unitDiffAtoms(c);
        if (ab != null) {
            return withDiff(ab[0], ab[1], g.constant().negate());   // a - b <= -const
        }
        // Neither shape holds it — a sum of two lengths, say. Keeping the form as written is what lets
        // a guard restating an invariant discharge it, which is the promise the flagging rests on.
        List<Asserted> next = new ArrayList<>(kept);
        next.add(new Asserted(g, strict));
        return new NumericDomain(false, lo, hi, diff, List.copyOf(next));
    }

    /** The two atoms of a unit difference {@code {a:+1, b:-1}} as {@code {a, b}}, or {@code null} if
     * {@code c} is not a two-atom form with coefficients +1 and -1. */
    private static String[] unitDiffAtoms(Map<String, BigDecimal> c) {
        if (c.size() != 2) {
            return null;
        }
        String a = null;
        String b = null;
        for (Map.Entry<String, BigDecimal> e : c.entrySet()) {
            if (e.getValue().compareTo(BigDecimal.ONE) == 0) {
                a = e.getKey();
            } else if (e.getValue().compareTo(BigDecimal.ONE.negate()) == 0) {
                b = e.getKey();
            } else {
                return null;
            }
        }
        return a != null && b != null ? new String[] {a, b} : null;
    }

    /** True for {@code GT}/{@code LT} (a strict comparison). */
    private static boolean strictOf(Rel rel) {
        return rel == Rel.GT || rel == Rel.LT;
    }

    /** True for {@code GE}/{@code GT} — the form is negated to reduce the comparison to {@code <= 0}. */
    private static boolean negOf(Rel rel) {
        return rel == Rel.GE || rel == Rel.GT;
    }

    // --- entails / refutes ---------------------------------------------------------------------

    /** Whether the domain proves {@code f rel 0} (the construction's invariant is discharged). */
    public boolean entails(LinearForm f, Rel rel) {
        if (bottom) {
            return true;   // an infeasible path discharges anything
        }
        if (rel == Rel.EQ) {
            return proveLe(f, false) && proveLe(f.negate(), false);
        }
        if (rel == Rel.NE) {
            return proveLe(f, true) || proveLe(f.negate(), true);   // f < 0, or f > 0
        }
        return proveLe(negOf(rel) ? f.negate() : f, strictOf(rel));
    }

    /** Whether the domain proves {@code ¬(f rel 0)} — the invariant is <em>definitely</em> violated
     * on this path (a compile error, the path-sensitive generalization of the constant check). The
     * negation flips both bits of the comparison: {@code ¬(f >= 0)} is {@code f < 0}, etc. */
    public boolean refutes(LinearForm f, Rel rel) {
        if (bottom || rel == Rel.EQ) {
            return false;   // an unreachable path violates nothing; equality is never refuted here
        }
        if (rel == Rel.NE) {
            return entails(f, Rel.EQ);   // proving it equal is proving it not unequal
        }
        return proveLe(negOf(rel) ? f : f.negate(), !strictOf(rel));
    }

    /** Whether {@code g <= 0} (or {@code g < 0} when strict) follows from the domain. */
    private boolean proveLe(LinearForm g, boolean strict) {
        BigDecimal hiG = upperBound(g);
        if (hiG != null) {
            int s = hiG.signum();
            if (strict ? s < 0 : s <= 0) {
                return true;
            }
        }
        String[] ab = unitDiffAtoms(g.coefs());
        if (ab != null) {
            BigDecimal diffBound = closedDiff(ab[0], ab[1]);   // proven upper bound on (a - b)
            if (diffBound != null) {
                BigDecimal bound = g.constant().negate();      // want a - b <= -const
                int s = diffBound.compareTo(bound);
                if (s < 0 || (!strict && s == 0)) {
                    return true;
                }
            }
        }
        // A form kept as written proves `g <= 0` when g is that form plus a constant no greater than
        // zero: asserting `f <= 0` gives `f + c <= 0` for every `c <= 0`.
        for (Asserted a : kept) {
            LinearForm slack = g.minus(a.f());
            if (!slack.coefs().isEmpty()) {
                continue;
            }
            int s = slack.constant().signum();
            if (s < 0 || (s == 0 && (!strict || a.strict()))) {
                return true;
            }
        }
        return false;
    }

    /** The interval upper bound of {@code f}, or {@code null} if unbounded above. */
    private BigDecimal upperBound(LinearForm f) {
        BigDecimal acc = f.constant();
        for (Map.Entry<String, BigDecimal> e : f.coefs().entrySet()) {
            BigDecimal k = e.getValue();
            BigDecimal b = k.signum() > 0 ? bestHi(e.getKey()) : bestLo(e.getKey());
            if (b == null) {
                return null;   // unbounded in the contributing direction
            }
            acc = acc.add(k.multiply(b));
        }
        return acc;
    }

    /** The tightest upper bound on an atom: its own, or one reached through a difference —
     * {@code a - b <= d} and {@code b <= c} give {@code a <= c + d}, which is what relates the size of
     * a filtered list to a bound on the list it came from. */
    private BigDecimal bestHi(String a) {
        BigDecimal best = hi.get(a);
        for (Map.Entry<String, BigDecimal> b : hi.entrySet()) {
            if (b.getKey().equals(a)) {
                continue;
            }
            BigDecimal d = closedDiff(a, b.getKey());
            if (d == null) {
                continue;
            }
            BigDecimal through = b.getValue().add(d);
            best = best == null ? through : min(best, through);
        }
        return best;
    }

    /** The tightest lower bound on an atom, the same way: {@code b - a <= d} and {@code b >= c} give
     * {@code a >= c - d}. */
    private BigDecimal bestLo(String a) {
        BigDecimal best = lo.get(a);
        for (Map.Entry<String, BigDecimal> b : lo.entrySet()) {
            if (b.getKey().equals(a)) {
                continue;
            }
            BigDecimal d = closedDiff(b.getKey(), a);
            if (d == null) {
                continue;
            }
            BigDecimal through = b.getValue().subtract(d);
            best = best == null ? through : max(best, through);
        }
        return best;
    }

    // --- assignment ----------------------------------------------------------------------------

    /** The domain after {@code atom := f}: drop every prior fact about {@code atom}, then record its
     * new interval bounds from {@code f} (relational facts about {@code f} are not re-derived). */
    public NumericDomain assign(String atom, LinearForm f) {
        if (bottom) {
            return this;
        }
        NumericDomain d = forget(atom);
        BigDecimal up = d.upperBound(f);
        BigDecimal down = negOrNull(d.upperBound(f.negate()));
        NumericDomain r = d;
        if (up != null) {
            r = r.withHi(atom, up);
        }
        if (down != null) {
            r = r.withLo(atom, down);
        }
        return r;
    }

    private static BigDecimal negOrNull(BigDecimal v) {
        return v == null ? null : v.negate();
    }

    /** The domain with every fact about {@code atom} dropped — what an assignment leaves behind of
     * what it assigns to. */
    private NumericDomain forget(String atom) {
        if (bottom) {
            return this;
        }
        Map<String, BigDecimal> nlo = new HashMap<>(lo);
        Map<String, BigDecimal> nhi = new HashMap<>(hi);
        nlo.remove(atom);
        nhi.remove(atom);
        Map<String, Map<String, BigDecimal>> nd = new HashMap<>();
        diff.forEach((a, row) -> {
            if (!a.equals(atom)) {
                Map<String, BigDecimal> nr = new HashMap<>(row);
                nr.remove(atom);
                if (!nr.isEmpty()) {
                    nd.put(a, nr);
                }
            }
        });
        List<Asserted> nk = new ArrayList<>(kept);
        nk.removeIf(a -> a.f().coefs().containsKey(atom));
        return new NumericDomain(false, nlo, nhi, nd, List.copyOf(nk));
    }

    // --- immutable updates ---------------------------------------------------------------------

    private NumericDomain bottom() {
        return new NumericDomain(true, Map.of(), Map.of(), Map.of(), List.of());
    }

    private NumericDomain withHi(String a, BigDecimal bound) {
        Map<String, BigDecimal> nhi = new HashMap<>(hi);
        nhi.merge(a, bound, NumericDomain::min);
        NumericDomain d = new NumericDomain(false, lo, nhi, diff, kept);
        return d.feasible() ? d : bottom();
    }

    private NumericDomain withLo(String a, BigDecimal bound) {
        Map<String, BigDecimal> nlo = new HashMap<>(lo);
        nlo.merge(a, bound, NumericDomain::max);
        NumericDomain d = new NumericDomain(false, nlo, hi, diff, kept);
        return d.feasible() ? d : bottom();
    }

    private NumericDomain withDiff(String a, String b, BigDecimal bound) {
        Map<String, Map<String, BigDecimal>> nd = new HashMap<>();
        diff.forEach((k, v) -> nd.put(k, new HashMap<>(v)));
        nd.computeIfAbsent(a, k -> new HashMap<>()).merge(b, bound, NumericDomain::min);
        NumericDomain d = new NumericDomain(false, lo, hi, nd, kept);
        return d.feasible() ? d : bottom();
    }

    /**
     * Whether the bounds and the differences can hold at once. Guards that contradict make the path
     * infeasible, and the domain must say so: {@link #entails} then discharges everything and
     * {@link #refutes} fires nothing, so nothing is reported at a construction that is not reached.
     *
     * <p>A bound is an edge to or from zero, so the two ways a contradiction shows up are one thing
     * seen twice: a difference cycle whose sum is negative, and a lower bound above an upper one once
     * the differences between them are closed. Deriving a bound through a difference is what made the
     * second reachable — {@code a <= b} and {@code b <= 0} bound {@code a} without recording anything
     * about {@code a} — so both are asked here rather than at the atom the assertion happened to name.
     */
    private boolean feasible() {
        for (Map.Entry<String, Map<String, BigDecimal>> row : closed().entrySet()) {
            BigDecimal cycle = row.getValue().get(row.getKey());
            if (cycle != null && cycle.signum() < 0) {
                return false;
            }
        }
        for (String a : lo.keySet()) {
            BigDecimal l = bestLo(a);
            BigDecimal h = bestHi(a);
            if (l != null && h != null && l.compareTo(h) > 0) {
                return false;
            }
        }
        return true;
    }

    /** The tightest proven upper bound on {@code a - b}, or {@code null} if none is known. */
    private BigDecimal closedDiff(String a, String b) {
        if (a.equals(b)) {
            return BigDecimal.ZERO;
        }
        Map<String, BigDecimal> row = closed().get(a);
        return row == null ? null : row.get(b);
    }

    /** The difference facts closed transitively — {@code a - b <= c} with {@code b - d <= e} gives
     * {@code a - d <= c + e} — computed once for the domain and read by every query it answers, since
     * a bound on one atom is derived through the differences to every other. */
    private Map<String, Map<String, BigDecimal>> closed() {
        if (closed == null) {
            closed = close(diff);
        }
        return closed;
    }

    private static Map<String, Map<String, BigDecimal>> close(Map<String, Map<String, BigDecimal>> diff) {
        Set<String> atoms = new HashSet<>(diff.keySet());
        diff.values().forEach(r -> atoms.addAll(r.keySet()));
        Map<String, Map<String, BigDecimal>> d = new HashMap<>();
        diff.forEach((a, row) -> d.put(a, new HashMap<>(row)));
        for (String through : atoms) {
            Map<String, BigDecimal> from = d.get(through);
            if (from == null) {
                continue;
            }
            List<Map.Entry<String, BigDecimal>> hops = List.copyOf(from.entrySet());
            for (String a : atoms) {
                if (a.equals(through)) {
                    continue;   // a hop from an atom to itself only repeats a cycle already recorded
                }
                BigDecimal toThrough = edge(d, a, through);
                if (toThrough == null) {
                    continue;
                }
                for (Map.Entry<String, BigDecimal> hop : hops) {
                    BigDecimal candidate = toThrough.add(hop.getValue());
                    BigDecimal known = edge(d, a, hop.getKey());
                    if (known == null || candidate.compareTo(known) < 0) {
                        d.computeIfAbsent(a, k -> new HashMap<>()).put(hop.getKey(), candidate);
                    }
                }
            }
        }
        return d;
    }

    private static BigDecimal edge(Map<String, Map<String, BigDecimal>> d, String a, String b) {
        Map<String, BigDecimal> row = d.get(a);
        return row == null ? null : row.get(b);
    }

    private static BigDecimal min(BigDecimal x, BigDecimal y) {
        return x.compareTo(y) <= 0 ? x : y;
    }

    private static BigDecimal max(BigDecimal x, BigDecimal y) {
        return x.compareTo(y) >= 0 ? x : y;
    }
}
