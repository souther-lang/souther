package souther.compiler.inputs;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;

/**
 * Linear constraints over two whole numbers, and which values of one of them have a whole number
 * of the other beside them.
 *
 * <p>About integer points and about nothing else. That a point satisfies every constraint here is
 * no claim that a value of the model stands there: the constraints are what a reader took from the
 * declarations and the way, and the points they leave may be more than the rows there are. A
 * {@link Shadow} is therefore a fact of the constraints, and it is a fact of the rows only where
 * the reader that built them shows the two the same ({@link RowsOfTheWay}).
 *
 * <p>Each constraint is held as {@code a·x + b·y <= c} with whole {@code a}, {@code b} and
 * {@code c}, divided through by what {@code a} and {@code b} share with {@code c} rounded down: on
 * whole numbers that says the same, so {@code e < 2p} and {@code 2e < 4p} are one constraint.
 * Every sum is exact.
 *
 * <p><b>Which {@code x} have a {@code y}.</b> Fixing {@code x} leaves {@code y} between the
 * greatest of its lower bounds and the least of its upper bounds, each rounded to a whole number,
 * and some {@code y} is there where every lower bound is at most every upper bound. A bound
 * rounds by the coefficient of {@code y} it was divided by, so it repeats its pattern from one
 * {@code x} to the next that many on and is a line on each residue class of {@code x} modulo
 * their least common multiple. Over a class every pair's condition is one linear condition on the
 * step along it, so the {@code x} the class holds are a run of its steps, and the {@code x} of all
 * of them are what this answers: exactly a run when the classes' runs fill the one run between
 * their least and greatest, and no answer when they do not (the even numbers are not a run).
 * More bounds than {@link #MOST_BOUNDS}, more classes than {@link #MOST_CLASSES}, or more pairs
 * of bounds over all the classes than {@link #MOST_STEPS}, is no answer either, and says which
 * limit was reached ({@link Shadow.OverTheLimit}).
 */
public final class TwoIntegerConstraints<A> {

    /** The most residue classes of one question: a larger least common multiple of the
     *  coefficients of the other number is not worked out. */
    public static final int MOST_CLASSES = 4096;

    /** The most bounds one question holds: pairs of them are asked, so the work is their square. */
    public static final int MOST_BOUNDS = 64;

    /** The most steps of one question: a pair of bounds at a residue class is one, so a few
     *  classes of many bounds and many classes of a few are each worked out. */
    public static final int MOST_STEPS = 1 << 17;

    /** Which limit of a question was reached. */
    public enum Limit { CLASSES, BOUNDS, STEPS }

    /**
     * The whole numbers of one of the two that have a whole number of the other beside them.
     *
     * <p>{@link Run} is both halves of a statement at once, and each is an exact fact of the
     * constraints: every number of the run has a partner, and no number outside it has.
     */
    public sealed interface Shadow {

        /** No number has a partner: the constraints leave no point. */
        record Nothing() implements Shadow {}

        /**
         * Exactly the numbers from {@code least} to {@code greatest} have a partner, an end null
         * where nothing bounds it.
         */
        record Run(BigInteger least, BigInteger greatest) implements Shadow {}

        /** Worked out: the numbers that have a partner are some, and no run (the even numbers). */
        record NotARun() implements Shadow {}

        /**
         * More was asked than a question is worked out in, and {@code limit} is the one that was
         * reached, so nothing is said of the numbers that have a partner: they may be a run, or
         * none.
         */
        record OverTheLimit(Limit limit) implements Shadow {}
    }

    /** One constraint: {@code form rel 0}. */
    public record Constraint<A>(LinearForm<A> form, Rel rel) {}

    /** {@code a·x + b·y <= c}. */
    private record Bound(BigInteger a, BigInteger b, BigInteger c) {}

    private final A x;
    private final A y;
    private final List<Bound> bounds;

    private TwoIntegerConstraints(A x, A y, List<Bound> bounds) {
        this.x = x;
        this.y = y;
        this.bounds = bounds;
    }

    /**
     * The constraints {@code given} over {@code first} and {@code second}, or null where one is
     * not about these two alone, holds one of them apart from a value ({@code !=}), or comes to
     * more constraints than are worked out.
     */
    public static <A> TwoIntegerConstraints<A> of(A first, A second,
                                                  List<Constraint<A>> given) {
        if (first.equals(second)) {
            // One number twice would put every coefficient of it on both, and ask a different
            // question than the constraints state: a call that has the one number has no business
            // here, and it is no constraint that is not worked out.
            throw new IllegalArgumentException("two numbers, and one given twice: " + first);
        }
        TwoIntegerConstraints<A> held = new TwoIntegerConstraints<>(first, second, List.of());
        for (Constraint<A> each : given) {
            held = held.with(each.form(), each.rel());
            if (held == null) {
                return null;
            }
        }
        return held;
    }

    /** These constraints and {@code form rel 0}, or null as {@link #of} says. */
    public TwoIntegerConstraints<A> with(LinearForm<A> form, Rel rel) {
        if (rel == Rel.NE || !form.coefs().keySet().stream()
                .allMatch(each -> each.equals(x) || each.equals(y))) {
            return null;
        }
        // Over whole numbers, with every coefficient and the constant scaled to whole ones by what
        // their denominators share.
        List<BigInteger[]> parts = new ArrayList<>();
        BigInteger scale = BigInteger.ONE;
        for (ExactRatio each : List.of(coefficient(form, x), coefficient(form, y),
                form.constant())) {
            BigInteger[] fraction = fractionOf(each);
            if (fraction == null) {
                return null;
            }
            parts.add(fraction);
            scale = scale.divide(scale.gcd(fraction[1])).multiply(fraction[1]);
        }
        BigInteger a = parts.get(0)[0].multiply(scale.divide(parts.get(0)[1]));
        BigInteger b = parts.get(1)[0].multiply(scale.divide(parts.get(1)[1]));
        BigInteger k = parts.get(2)[0].multiply(scale.divide(parts.get(2)[1]));
        List<Bound> next = new ArrayList<>(bounds);
        // a·x + b·y + k rel 0, and the scale is positive so no relation turns.
        switch (rel) {
            case LE -> next.add(bound(a, b, k.negate()));
            case LT -> next.add(bound(a, b, k.negate().subtract(BigInteger.ONE)));
            case GE -> next.add(bound(a.negate(), b.negate(), k));
            case GT -> next.add(bound(a.negate(), b.negate(), k.subtract(BigInteger.ONE)));
            case EQ -> {
                next.add(bound(a, b, k.negate()));
                next.add(bound(a.negate(), b.negate(), k));
            }
            case NE -> throw new IllegalStateException("refused above");
        }
        List<Bound> kept = new ArrayList<>(new LinkedHashSet<>(next));
        return new TwoIntegerConstraints<>(x, y, kept);
    }

    /**
     * Which values of {@code axis}, one of the two, have a whole number of the other beside them.
     */
    public Shadow shadowOn(A axis) {
        if (axis.equals(x)) {
            return shadow(bounds);
        }
        if (!axis.equals(y)) {
            throw new IllegalArgumentException("not one of the two numbers: " + axis);
        }
        return shadow(bounds.stream().map(each -> new Bound(each.b(), each.a(), each.c()))
                .toList());
    }

    private static Bound bound(BigInteger a, BigInteger b, BigInteger c) {
        BigInteger shared = a.gcd(b);
        if (shared.signum() == 0) {
            // 0 <= c: held or never.
            return new Bound(BigInteger.ZERO, BigInteger.ZERO,
                    c.signum() >= 0 ? BigInteger.ZERO : BigInteger.ONE.negate());
        }
        return new Bound(a.divide(shared), b.divide(shared), floorDivide(c, shared));
    }

    private static Shadow shadow(List<Bound> all) {
        if (all.size() > MOST_BOUNDS) {
            return new Shadow.OverTheLimit(Limit.BOUNDS);
        }
        List<Bound> lower = new ArrayList<>();
        List<Bound> upper = new ArrayList<>();
        List<Bound> alone = new ArrayList<>();
        for (Bound each : all) {
            if (each.a().signum() == 0 && each.b().signum() == 0) {
                if (each.c().signum() < 0) {
                    return new Shadow.Nothing();
                }
            } else if (each.b().signum() == 0) {
                alone.add(each);
            } else if (each.b().signum() > 0) {
                upper.add(each);
            } else {
                lower.add(each);
            }
        }
        // The step the classes repeat on: the coefficients of y the bounds were divided by.
        // Where y is bounded on one side only there is no pair to round against.
        BigInteger period = BigInteger.ONE;
        if (!lower.isEmpty() && !upper.isEmpty()) {
            for (Bound each : lower) {
                period = lcm(period, each.b().negate());
            }
            for (Bound each : upper) {
                period = lcm(period, each.b());
            }
        }
        if (period.compareTo(BigInteger.valueOf(MOST_CLASSES)) > 0) {
            return new Shadow.OverTheLimit(Limit.CLASSES);
        }
        int classes = period.intValueExact();
        // The work is the pairs of bounds asked at every class, which neither limit above bounds
        // by itself.
        if ((long) classes * (1L * lower.size() * upper.size() + alone.size() + 1) > MOST_STEPS) {
            return new Shadow.OverTheLimit(Limit.STEPS);
        }
        BigInteger[][] slopes = slopesOf(period, lower, upper);
        BigInteger[][] steps = new BigInteger[classes][];
        BigInteger least = null;
        BigInteger greatest = null;
        boolean unboundedBelow = false;
        boolean unboundedAbove = false;
        boolean any = false;
        for (int residue = 0; residue < classes; residue++) {
            BigInteger[] range = stepsOfClass(BigInteger.valueOf(residue), period, lower, upper,
                    alone, slopes);
            steps[residue] = range;
            if (range == EMPTY) {
                continue;
            }
            any = true;
            BigInteger r = BigInteger.valueOf(residue);
            if (range[0] == null) {
                unboundedBelow = true;
            } else {
                BigInteger first = r.add(period.multiply(range[0]));
                least = (least == null || first.compareTo(least) < 0) ? first : least;
            }
            if (range[1] == null) {
                unboundedAbove = true;
            } else {
                BigInteger last = r.add(period.multiply(range[1]));
                greatest = (greatest == null || last.compareTo(greatest) > 0) ? last : greatest;
            }
        }
        if (!any) {
            return new Shadow.Nothing();
        }
        BigInteger from = unboundedBelow ? null : least;
        BigInteger to = unboundedAbove ? null : greatest;
        // A run only where every class holds every one of its numbers between the two ends.
        for (int residue = 0; residue < classes; residue++) {
            if (!classFillsTheRun(BigInteger.valueOf(residue), period, steps[residue], from, to)) {
                return new Shadow.NotARun();
            }
        }
        return new Shadow.Run(from, to);
    }

    private static final BigInteger[] EMPTY = new BigInteger[0];

    /**
     * The steps {@code t} for which {@code residue + period·t} has a whole number beside it, as the
     * least and greatest, an end null where nothing bounds it; {@link #EMPTY} where there are none.
     */
    private static BigInteger[] stepsOfClass(BigInteger residue, BigInteger period,
                                             List<Bound> lower, List<Bound> upper,
                                             List<Bound> alone, BigInteger[][] slopes) {
        BigInteger[] steps = {null, null};
        for (Bound each : alone) {
            // a·x <= c.
            if (!narrow(steps, each.a().multiply(period),
                    each.c().subtract(each.a().multiply(residue)))) {
                return EMPTY;
            }
        }
        // Each bound at the class once, and not once for every pair it is in:
        // ceil((a_l·x - c_l) / beta) <= floor((c_u - a_u·x) / gamma), beta and gamma the
        // coefficients of y, with x = residue + period·t.
        BigInteger[] ceilLow = new BigInteger[lower.size()];
        for (int at = 0; at < ceilLow.length; at++) {
            Bound low = lower.get(at);
            ceilLow[at] = ceilDivide(low.a().multiply(residue).subtract(low.c()),
                    low.b().negate());
        }
        BigInteger[] floorUp = new BigInteger[upper.size()];
        for (int at = 0; at < floorUp.length; at++) {
            Bound up = upper.get(at);
            floorUp[at] = floorDivide(up.c().subtract(up.a().multiply(residue)), up.b());
        }
        for (int low = 0; low < ceilLow.length; low++) {
            for (int up = 0; up < floorUp.length; up++) {
                if (!narrow(steps, slopes[low][up], floorUp[up].subtract(ceilLow[low]))) {
                    return EMPTY;
                }
            }
        }
        return steps;
    }

    /** How the step along a class moves the condition of each pair of a lower and an upper bound:
     *  the same at every class, so worked out once. */
    private static BigInteger[][] slopesOf(BigInteger period, List<Bound> lower,
                                           List<Bound> upper) {
        BigInteger[][] slopes = new BigInteger[lower.size()][upper.size()];
        for (int low = 0; low < slopes.length; low++) {
            for (int up = 0; up < slopes[low].length; up++) {
                Bound below = lower.get(low);
                Bound above = upper.get(up);
                slopes[low][up] = above.a().multiply(period.divide(above.b()))
                        .add(below.a().multiply(period.divide(below.b().negate())));
            }
        }
        return slopes;
    }

    /** {@code steps} held to {@code slope·t <= limit}; false where that leaves no step. */
    private static boolean narrow(BigInteger[] steps, BigInteger slope, BigInteger limit) {
        if (slope.signum() == 0) {
            return limit.signum() >= 0;
        }
        if (slope.signum() > 0) {
            BigInteger most = floorDivide(limit, slope);
            steps[1] = (steps[1] == null || most.compareTo(steps[1]) < 0) ? most : steps[1];
        } else {
            BigInteger fewest = ceilDivide(limit, slope);
            steps[0] = (steps[0] == null || fewest.compareTo(steps[0]) > 0) ? fewest : steps[0];
        }
        return steps[0] == null || steps[1] == null || steps[0].compareTo(steps[1]) <= 0;
    }

    /**
     * Whether the numbers of this class between {@code from} and {@code to}, an end null where
     * nothing bounds it, are exactly the numbers of its steps.
     */
    private static boolean classFillsTheRun(BigInteger residue, BigInteger period,
                                            BigInteger[] steps, BigInteger from, BigInteger to) {
        if (steps == EMPTY) {
            // No number of the class has a partner, so none may lie in the run.
            if (from == null || to == null) {
                return false;
            }
            return ceilDivide(from.subtract(residue), period)
                    .compareTo(floorDivide(to.subtract(residue), period)) > 0;
        }
        boolean below = from == null
                ? steps[0] == null
                : steps[0] != null
                        && steps[0].equals(ceilDivide(from.subtract(residue), period));
        boolean above = to == null
                ? steps[1] == null
                : steps[1] != null
                        && steps[1].equals(floorDivide(to.subtract(residue), period));
        return below && above;
    }

    private static BigInteger lcm(BigInteger one, BigInteger other) {
        return one.divide(one.gcd(other)).multiply(other);
    }

    private static BigInteger floorDivide(BigInteger number, BigInteger by) {
        BigInteger[] qr = number.divideAndRemainder(by);
        return qr[1].signum() != 0 && (qr[1].signum() != by.signum())
                ? qr[0].subtract(BigInteger.ONE) : qr[0];
    }

    private static BigInteger ceilDivide(BigInteger number, BigInteger by) {
        BigInteger[] qr = number.divideAndRemainder(by);
        return qr[1].signum() != 0 && (qr[1].signum() == by.signum())
                ? qr[0].add(BigInteger.ONE) : qr[0];
    }

    private ExactRatio coefficient(LinearForm<A> form, A of) {
        Map<A, ExactRatio> coefs = form.coefs();
        ExactRatio found = coefs.get(of);
        return found == null ? ExactRatio.ZERO : found;
    }

    /**
     * {@code ratio} as a whole numerator over a positive whole denominator in lowest terms, which
     * the ratio says ({@link ExactRatio#asTerms}); null where either is too large to hold.
     */
    private static BigInteger[] fractionOf(ExactRatio ratio) {
        ExactRatio.Terms terms = ratio.asTerms();
        BigInteger numerator = terms.comesTo().floor().orNull();
        BigInteger denominator = terms.per().floor().orNull();
        return (numerator == null || denominator == null) ? null
                : new BigInteger[] {numerator, denominator};
    }
}
