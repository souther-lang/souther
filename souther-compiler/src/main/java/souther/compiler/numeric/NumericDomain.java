package souther.compiler.numeric;

import souther.compiler.numeric.Place;
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
 * interval + difference-bound; a form of neither shape is kept as it was written and nothing is
 * derived from it on its own, but it stands as a premise wherever the derived part proves the
 * difference between it and what is being asked (spec §invariant-discharge). Instances are
 * immutable — each operation returns a fresh domain, threaded functionally like
 * {@code TotalityChecker}'s scope map.
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
    private final Map<String, Endpoint> lo;                    // atom -> lower bound (absent = -inf)
    private final Map<String, Endpoint> hi;                    // atom -> upper bound (absent = +inf)
    private final Map<String, Map<String, Endpoint>> diff;     // diff[a][b] = tightest known (a - b)
    private final List<Asserted> kept;                         // forms outside both shapes, as written
    private final Map<String, Granularity> kinds;              // atom -> how its values are spaced
    private final Map<String, Set<Loss>> losses;               // atom -> what was not recorded of it
    private Map<String, Map<String, Endpoint>> closed;         // diff closed transitively, on first ask

    private NumericDomain(boolean bottom, Map<String, Endpoint> lo, Map<String, Endpoint> hi,
                          Map<String, Map<String, Endpoint>> diff, List<Asserted> kept,
                          Map<String, Granularity> kinds, Map<String, Set<Loss>> losses) {
        this.bottom = bottom;
        this.lo = lo;
        this.hi = hi;
        this.diff = diff;
        this.kept = kept;
        this.kinds = kinds;
        this.losses = losses;
    }

    public static NumericDomain top() {
        return new NumericDomain(false, Map.of(), Map.of(), Map.of(), List.of(), Map.of(), Map.of());
    }

    /**
     * A way an assertion arrived holding more than the domain kept of it.
     *
     * <p>Recorded where it happens rather than read back afterwards. What the bounds say is sound
     * either way — everything dropped here was a narrowing, and a wider bound proves less — but a
     * caller turning a bound into a value somebody has to write needs to know the edge is where the
     * rules stop and not merely where this stopped reading them.
     */
    public enum Loss {

        /** A disequality. {@code x /= 0} is a hole in a range, and a range is all this holds. */
        DROPPED_DISEQUALITY,

        /** A form that is neither an interval nor a difference, kept as written. It proves things
         * ({@link #entails} reads it, as a premise as well as a match) and no bound is derived
         * through it — {@link #boundsOf} does not read it, so a projection is short of what the
         * rules said. */
        KEPT_UNPROJECTABLE
    }

    public boolean isBottom() {
        return bottom;
    }

    // --- assume: tighten along `f rel 0` -------------------------------------------------------

    /**
     * The domain refined by asserting {@code f rel 0}.
     *
     * @param atomKinds how the values of each atom of {@code f} are spaced. Required rather than
     *                  defaulted: an atom whose spacing is guessed is one a strict bound is either
     *                  wrongly sharpened on or silently left blunt, and neither shows up as a
     *                  failure anywhere near where the guess was made.
     */
    public NumericDomain assume(LinearForm f, Rel rel, Map<String, Granularity> atomKinds) {
        NumericDomain d = knowing(f.coefs().keySet(), atomKinds);
        if (d.bottom) {
            return d;
        }
        if (rel == Rel.NE) {
            // `f != 0` is a disjunction, and the domain holds conjunctions of bounds. Nothing to
            // record; what settles such a guard is the fact keyed on the comparison itself.
            return f.coefs().isEmpty() ? d
                    : d.losing(Loss.DROPPED_DISEQUALITY, f.coefs().keySet());
        }
        if (rel == Rel.EQ) {
            return d.addLe(f, false).addLe(f.negate(), false);
        }
        // Reduce `f rel 0` to `g <= 0` (or `g < 0`): negate the form for >=/>, keep it for <=/<.
        return d.addLe(negOf(rel) ? f.negate() : f, strictOf(rel));
    }

    /**
     * The domain with the spacing of each of {@code atoms} recorded.
     *
     * <p>One atom is one kind of number for as long as the domain lives. The same key arriving as
     * both is not a widening to absorb — the key is what says two readings are of one value, so two
     * spacings under one key means the naming and the typing disagree, and the answer to that is to
     * stop rather than to pick the safer of the two.
     */
    private NumericDomain knowing(Set<String> atoms, Map<String, Granularity> atomKinds) {
        Map<String, Granularity> next = null;
        for (String atom : atoms) {
            Granularity given = atomKinds.get(atom);
            if (given == null) {
                throw new IllegalStateException("no granularity given for atom `" + atom + "`");
            }
            Granularity had = kinds.get(atom);
            if (had == given) {
                continue;
            }
            if (had != null) {
                throw new IllegalStateException(
                        "atom `" + atom + "` is " + had + " and " + given);
            }
            if (next == null) {
                next = new HashMap<>(kinds);
            }
            next.put(atom, given);
        }
        return next == null ? this
                : new NumericDomain(bottom, lo, hi, diff, kept, Map.copyOf(next), losses);
    }

    /**
     * Assert {@code g <= 0} (or {@code g < 0} when strict), updating an interval or a difference, or
     * keeping the form as written when it is neither.
     *
     * <p>What strictness is worth depends on what the atoms are made of. Over whole numbers there is
     * a next value to step to, so {@code a < 3} is {@code a <= 2} and {@code a - b < 0} is
     * {@code a - b <= -1}, and the end that lands there is one the rule admits. Over decimals there
     * is no step, and the end stays where the constraint put it and says that the value is not its
     * own. A form of neither shape keeps its strictness as written.
     */
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
            Endpoint end = kinds.get(a) == Granularity.DISCRETE
                    ? Endpoint.inclusive(whole(bound, upper, strict))
                    : new Endpoint(Count.of(bound), !strict);
            return upper ? withHi(a, end) : withLo(a, end);
        }
        String[] ab = unitDiffAtoms(c);
        if (ab != null) {
            // a - b <= -const. A difference of two whole numbers is a whole number, and only then:
            // one dense atom on either side leaves the difference with no smallest step, so the
            // bound stays where the constant put it and says the value is outside it.
            BigDecimal bound = g.constant().negate();
            Endpoint end = kinds.get(ab[0]) == Granularity.DISCRETE
                    && kinds.get(ab[1]) == Granularity.DISCRETE
                    ? Endpoint.inclusive(whole(bound, true, strict))
                    : new Endpoint(Count.of(bound), !strict);
            return withDiff(ab[0], ab[1], end);
        }
        // Neither shape holds it — a sum of two lengths, say. Keeping the form as written is what lets
        // a guard restating an invariant discharge it, which is the promise the flagging rests on.
        List<Asserted> next = new ArrayList<>(kept);
        next.add(new Asserted(g, strict));
        return new NumericDomain(false, lo, hi, diff, List.copyOf(next), kinds,
                with(Loss.KEPT_UNPROJECTABLE, c.keySet()));
    }

    /**
     * A bound on a whole number, tightened to one.
     *
     * <p>Never past the true bound. An upper bound admits everything up to {@code q}, so the largest
     * whole number it admits is {@code floor(q)}; a strict one stops short of {@code q}, so the
     * largest is the whole number below it, {@code ceil(q) - 1} — which is {@code q - 1} where
     * {@code q} is whole and {@code floor(q)} where it is not. Lower bounds are the mirror.
     *
     * @param q      the bound as the arithmetic left it, already rounded away from the constraint
     * @param upper  whether {@code q} bounds the atom above
     * @param strict whether the value {@code q} itself is outside what the constraint admits
     */
    private static Count whole(BigDecimal q, boolean upper, boolean strict) {
        Count at = Count.of(q);
        if (upper) {
            return strict ? at.rounded(java.math.RoundingMode.CEILING).minus(1)
                    : at.rounded(java.math.RoundingMode.FLOOR);
        }
        return strict ? at.rounded(java.math.RoundingMode.FLOOR).plus(1)
                : at.rounded(java.math.RoundingMode.CEILING);
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

    /**
     * Whether {@code g <= 0} (or {@code g < 0} when strict) follows from the domain.
     *
     * <p>Two ways to reach it, and the second reads the first. A form kept as written is a premise
     * and not only something a goal is matched against: {@code f <= 0} together with
     * {@code g - f <= 0} gives {@code g <= 0}, so a relation of neither shape carries onward wherever
     * the derived fragment proves the difference between it and the goal. That is what relates a
     * guard over a computed value to what the type of the value it was compared against guarantees —
     * the two land in different shapes, and neither is the other's to derive.
     *
     * <p>One premise, once. The residual is proven against the derived fragment alone
     * ({@link #proveBaseLe}), so two kept relations are never added together. Closing the kept
     * relations over each other is arbitrary linear reasoning and a different fragment to state; this
     * one is what the domain already decides in, reached through one relation it does not.
     */
    private boolean proveLe(LinearForm g, boolean strict) {
        if (proveBaseLe(g, strict)) {
            return true;
        }
        for (Asserted a : kept) {
            // The goal is strict where either the premise or the residual is, so what the residual is
            // asked for is what the premise did not already give.
            if (proveBaseLe(g.minus(a.f()), strict && !a.strict())) {
                return true;
            }
        }
        return false;
    }

    /** The same over what this derives in: an interval bound on the whole form, or a bound on a
     * difference of two atoms read through the closure. The kept relations are not read here — this
     * is what a residual is proven against, and reading them would let one stand on another. */
    private boolean proveBaseLe(LinearForm g, boolean strict) {
        Endpoint hiG = upperBound(g);
        if (hiG != null) {
            int s = at(hiG).signum();
            // An end at zero the form's own bounds do not reach proves the strict form: nothing the
            // domain admits gets there, which is what `g < 0` asks.
            if (s < 0 || (s == 0 && (!strict || !hiG.inclusive()))) {
                return true;
            }
        }
        String[] ab = unitDiffAtoms(g.coefs());
        if (ab != null) {
            Endpoint diffBound = closedDiff(ab[0], ab[1]);     // proven upper bound on (a - b)
            if (diffBound != null) {
                Count bound = Count.of(g.constant().negate());   // want a - b <= -const
                int s = at(diffBound).compareTo(bound);
                if (s < 0 || (s == 0 && (!strict || !diffBound.inclusive()))) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * The interval upper bound of {@code f}, or {@code null} if unbounded above.
     *
     * <p>The end is the form's own only where every end it was added from is. One term that cannot
     * reach its edge is one the sum cannot reach either, so a single exclusive contribution makes the
     * total exclusive.
     */
    private Endpoint upperBound(LinearForm f) {
        Count acc = Count.of(f.constant());
        boolean inclusive = true;
        for (Map.Entry<String, BigDecimal> e : f.coefs().entrySet()) {
            BigDecimal k = e.getValue();
            Endpoint b = k.signum() > 0 ? bestHi(e.getKey()) : bestLo(e.getKey());
            if (b == null) {
                return null;   // unbounded in the contributing direction
            }
            acc = acc.plus(at(b).times(k));
            inclusive &= b.inclusive();
        }
        return new Endpoint(acc, inclusive);
    }

    /** The tightest upper bound on an atom: its own, or one reached through a difference —
     * {@code a - b <= d} and {@code b <= c} give {@code a <= c + d}, which is what relates the size of
     * a filtered list to a bound on the list it came from. A value at the end reached that way needs
     * every end on the way to be reachable, so the derived end is its own only where both are. */
    private Endpoint bestHi(String a) {
        Endpoint best = hi.get(a);
        for (Map.Entry<String, Endpoint> b : hi.entrySet()) {
            if (b.getKey().equals(a)) {
                continue;
            }
            Endpoint d = closedDiff(a, b.getKey());
            if (d == null) {
                continue;
            }
            best = Endpoint.upper(best, new Endpoint(at(b.getValue()).plus(at(d)),
                    b.getValue().inclusive() && d.inclusive()));
        }
        return best;
    }

    /** The tightest lower bound on an atom, the same way: {@code b - a <= d} and {@code b >= c} give
     * {@code a >= c - d}. */
    private Endpoint bestLo(String a) {
        Endpoint best = lo.get(a);
        for (Map.Entry<String, Endpoint> b : lo.entrySet()) {
            if (b.getKey().equals(a)) {
                continue;
            }
            Endpoint d = closedDiff(b.getKey(), a);
            if (d == null) {
                continue;
            }
            best = Endpoint.lower(best, new Endpoint(at(b.getValue()).minus(at(d)),
                    b.getValue().inclusive() && d.inclusive()));
        }
        return best;
    }

    // --- reading the domain back ------------------------------------------------------------------

    /**
     * The tightest bounds this proves on one atom, {@code null} at either end where it proves none.
     *
     * <p>Through the differences, not off the atom's own record: {@code a - b <= 0} with
     * {@code b <= 1440} bounds {@code a} at 1440 though nothing was ever asserted about {@code a}
     * alone. That is the whole point of asking here rather than reading what was put in.
     */
    public Bounds boundsOf(String atom) {
        return bottom ? new Bounds(null, null) : new Bounds(bestLo(atom), bestHi(atom));
    }

    /**
     * The count an end is at.
     *
     * <p>Every end this holds was built from a number here, so this is a statement of that and not a
     * check on a caller: an atom is a position the rules relate arithmetically, and a position whose
     * values are not numbers has no atom to be related through.
     */
    private static Count at(Endpoint end) {
        if (!(end.at() instanceof Count count)) {
            throw new IllegalStateException("an atom's end is not a number: " + end);
        }
        return count;
    }

    /** What an atom's values are known to lie between. A {@code null} end is unbounded there. */
    public record Bounds(Endpoint min, Endpoint max) {

        public boolean isEmpty() {
            return min == null && max == null;
        }

        /** Whether {@code at} is inside both ends — asked of the ends, because whether an end is one
         * of the counts it stops at is what the number alone does not say. */
        public boolean admits(Place at) {
            return (min == null || Endpoint.someValueLiesBetween(min, Endpoint.inclusive(at)))
                    && (max == null || Endpoint.someValueLiesBetween(Endpoint.inclusive(at), max));
        }
    }

    /**
     * Whether everything this holds is held in a shape {@link #boundsOf} reads.
     *
     * <p>False where anything asserted into it narrowed more than a bound could hold: see
     * {@link Loss}. A caller turning a projection into a value somebody has to write has to know
     * which of the two it has.
     */
    public boolean projectionIsLossless() {
        return losses.isEmpty();
    }

    /**
     * Whether the bounds on one atom are the whole of what the rules about it say.
     *
     * <p>Asked of the atom and not of the domain. A rule this could not hold is a rule about the
     * positions it names, and a bound on some other atom is as good as it ever was — a pattern on a
     * name says nothing about how many minutes a day has.
     */
    /** What was asserted about one atom and not recorded. */
    public Set<Loss> lossesAt(String atom) {
        return losses.getOrDefault(atom, Set.of());
    }

    /** Every atom something was lost about. */
    public Set<String> lossyAtoms() {
        return losses.keySet();
    }

    private NumericDomain losing(Loss loss, Set<String> atoms) {
        Map<String, Set<Loss>> next = with(loss, atoms);
        return next == losses ? this
                : new NumericDomain(bottom, lo, hi, diff, kept, kinds, next);
    }

    private Map<String, Set<Loss>> with(Loss loss, Set<String> atoms) {
        Map<String, Set<Loss>> next = null;
        for (String atom : atoms) {
            if (losses.getOrDefault(atom, Set.of()).contains(loss)) {
                continue;
            }
            if (next == null) {
                next = new HashMap<>(losses);
            }
            Set<Loss> here = java.util.EnumSet.noneOf(Loss.class);
            here.addAll(next.getOrDefault(atom, Set.of()));
            here.add(loss);
            next.put(atom, java.util.Collections.unmodifiableSet(here));
        }
        return next == null ? losses : Map.copyOf(next);
    }

    // --- assignment ----------------------------------------------------------------------------

    /** The domain after {@code atom := f}: drop every prior fact about {@code atom}, then record its
     * new interval bounds from {@code f} (relational facts about {@code f} are not re-derived). */
    public NumericDomain assign(String atom, LinearForm f, Map<String, Granularity> atomKinds) {
        Set<String> named = new HashSet<>(f.coefs().keySet());
        named.add(atom);
        NumericDomain known = knowing(named, atomKinds);
        if (known.bottom) {
            return known;
        }
        NumericDomain d = known.forget(atom);
        Endpoint up = d.upperBound(f);
        Endpoint down = negOrNull(d.upperBound(f.negate()));
        NumericDomain r = d;
        if (up != null) {
            r = r.withHi(atom, up);
        }
        if (down != null) {
            r = r.withLo(atom, down);
        }
        return r;
    }

    /** An upper bound on {@code -f} read as a lower bound on {@code f}. Turning it around moves the
     * value and not whether it is reached. */
    private static Endpoint negOrNull(Endpoint v) {
        return v == null ? null : new Endpoint(at(v).negate(), v.inclusive());
    }

    /** The domain with every fact about {@code atom} dropped — what an assignment leaves behind of
     * what it assigns to. */
    private NumericDomain forget(String atom) {
        if (bottom) {
            return this;
        }
        Map<String, Endpoint> nlo = new HashMap<>(lo);
        Map<String, Endpoint> nhi = new HashMap<>(hi);
        nlo.remove(atom);
        nhi.remove(atom);
        Map<String, Map<String, Endpoint>> nd = new HashMap<>();
        diff.forEach((a, row) -> {
            if (!a.equals(atom)) {
                Map<String, Endpoint> nr = new HashMap<>(row);
                nr.remove(atom);
                if (!nr.isEmpty()) {
                    nd.put(a, nr);
                }
            }
        });
        List<Asserted> nk = new ArrayList<>(kept);
        nk.removeIf(a -> a.f().coefs().containsKey(atom));
        return new NumericDomain(false, nlo, nhi, nd, List.copyOf(nk), kinds, losses);
    }

    // --- immutable updates ---------------------------------------------------------------------

    private NumericDomain bottom() {
        return new NumericDomain(true, Map.of(), Map.of(), Map.of(), List.of(), kinds, losses);
    }

    private NumericDomain withHi(String a, Endpoint bound) {
        Map<String, Endpoint> nhi = new HashMap<>(hi);
        nhi.merge(a, bound, Endpoint::upper);
        NumericDomain d = new NumericDomain(false, lo, nhi, diff, kept, kinds, losses);
        return d.feasible() ? d : bottom();
    }

    private NumericDomain withLo(String a, Endpoint bound) {
        Map<String, Endpoint> nlo = new HashMap<>(lo);
        nlo.merge(a, bound, Endpoint::lower);
        NumericDomain d = new NumericDomain(false, nlo, hi, diff, kept, kinds, losses);
        return d.feasible() ? d : bottom();
    }

    private NumericDomain withDiff(String a, String b, Endpoint bound) {
        Map<String, Map<String, Endpoint>> nd = new HashMap<>();
        diff.forEach((k, v) -> nd.put(k, new HashMap<>(v)));
        nd.computeIfAbsent(a, k -> new HashMap<>()).merge(b, bound, Endpoint::upper);
        NumericDomain d = new NumericDomain(false, lo, hi, nd, kept, kinds, losses);
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
        for (Map.Entry<String, Map<String, Endpoint>> row : closed().entrySet()) {
            Endpoint cycle = row.getValue().get(row.getKey());
            // `a - a` is zero, so a cycle bounding it below zero is a contradiction — and so is one
            // bounding it at zero without admitting it.
            if (cycle != null && (at(cycle).signum() < 0
                    || (at(cycle).signum() == 0 && !cycle.inclusive()))) {
                return false;
            }
        }
        for (String a : lo.keySet()) {
            if (!Endpoint.someValueLiesBetween(bestLo(a), bestHi(a))) {
                return false;
            }
        }
        return true;
    }

    /** The tightest proven upper bound on {@code a - b}, or {@code null} if none is known. */
    private Endpoint closedDiff(String a, String b) {
        if (a.equals(b)) {
            return Endpoint.inclusive(Count.ZERO);
        }
        Map<String, Endpoint> row = closed().get(a);
        return row == null ? null : row.get(b);
    }

    /** The difference facts closed transitively — {@code a - b <= c} with {@code b - d <= e} gives
     * {@code a - d <= c + e} — computed once for the domain and read by every query it answers, since
     * a bound on one atom is derived through the differences to every other. */
    private Map<String, Map<String, Endpoint>> closed() {
        if (closed == null) {
            closed = close(diff);
        }
        return closed;
    }

    private static Map<String, Map<String, Endpoint>> close(Map<String, Map<String, Endpoint>> diff) {
        Set<String> atoms = new HashSet<>(diff.keySet());
        diff.values().forEach(r -> atoms.addAll(r.keySet()));
        Map<String, Map<String, Endpoint>> d = new HashMap<>();
        diff.forEach((a, row) -> d.put(a, new HashMap<>(row)));
        for (String through : atoms) {
            Map<String, Endpoint> from = d.get(through);
            if (from == null) {
                continue;
            }
            List<Map.Entry<String, Endpoint>> hops = List.copyOf(from.entrySet());
            for (String a : atoms) {
                if (a.equals(through)) {
                    continue;   // a hop from an atom to itself only repeats a cycle already recorded
                }
                Endpoint toThrough = edge(d, a, through);
                if (toThrough == null) {
                    continue;
                }
                for (Map.Entry<String, Endpoint> hop : hops) {
                    // A path reaches its end only where every hop on it does.
                    Endpoint candidate = new Endpoint(
                            at(toThrough).plus(at(hop.getValue())),
                            toThrough.inclusive() && hop.getValue().inclusive());
                    Endpoint known = edge(d, a, hop.getKey());
                    if (known == null || Endpoint.upper(known, candidate) == candidate) {
                        d.computeIfAbsent(a, k -> new HashMap<>()).put(hop.getKey(), candidate);
                    }
                }
            }
        }
        return d;
    }

    private static Endpoint edge(Map<String, Map<String, Endpoint>> d, String a, String b) {
        Map<String, Endpoint> row = d.get(a);
        return row == null ? null : row.get(b);
    }
}
