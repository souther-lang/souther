package souther.compiler.numeric;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;

/**
 * A set of whole numbers as a union of progressions: the numbers of a run that leave one remainder
 * by one divisor.
 *
 * <p>What {@link WholeNumberRuns} holds is the progressions of divisor one, and what a relation
 * between a number and a weighed one leaves of it is more: {@code 2·x = c} has a solution exactly
 * where {@code c} is even. A set held by its ends and its remainders is exact both ways, and costs
 * what it has parts, so the numbers of a type that stops at the greatest {@code Int} are no
 * thousand millions of values here.
 *
 * <p>Membership and nearest members, and nothing about the order the parts are written in: two of
 * these holding the same numbers are not equal because nothing here joins what touches.
 *
 * @param parts the progressions, each with ends that are members of it
 */
public record WholeNumberSet(List<Part> parts) {

    /** The numbers of {@code run} that are in {@code within}, with ends that are members. */
    public record Part(WholeNumberRuns.Run run, Congruences within) {

        public Part {
            if (run == null || within == null) {
                throw new IllegalArgumentException("a progression is of a run and a remainder");
            }
            BigInteger from = run.from() == null ? null : within.leastAtOrAbove(run.from());
            BigInteger to = run.to() == null ? null : within.greatestAtOrBelow(run.to());
            if (from != null && to != null && from.compareTo(to) > 0) {
                throw new IllegalArgumentException("a progression holds a number: " + run
                        + " of " + within);
            }
            run = new WholeNumberRuns.Run(from, to);
        }

        /** The progression, or null where the run holds no number of the remainder. */
        static Part orNone(WholeNumberRuns.Run run, Congruences within) {
            BigInteger from = run.from() == null ? null : within.leastAtOrAbove(run.from());
            BigInteger to = run.to() == null ? null : within.greatestAtOrBelow(run.to());
            return from != null && to != null && from.compareTo(to) > 0 ? null
                    : new Part(run, within);
        }

        boolean holds(BigInteger number) {
            return run.holds(number) && within.greatestAtOrBelow(number).equals(number);
        }

        /** The greatest member at or below {@code number}, or null. */
        BigInteger atOrBelow(BigInteger number) {
            BigInteger at = within.greatestAtOrBelow(number);
            if (run.to() != null && at.compareTo(run.to()) > 0) {
                at = run.to();
            }
            return run.from() != null && at.compareTo(run.from()) < 0 ? null : at;
        }

        /** The least member at or above {@code number}, or null. */
        BigInteger atOrAbove(BigInteger number) {
            BigInteger at = within.leastAtOrAbove(number);
            if (run.from() != null && at.compareTo(run.from()) < 0) {
                at = run.from();
            }
            return run.to() != null && at.compareTo(run.to()) > 0 ? null : at;
        }
    }

    /** The congruences of divisor one, which every whole number is in. */
    private static final Congruences EVERY_NUMBER = new Congruences(BigInteger.ZERO,
            BigInteger.ONE);

    /** No number at all. */
    public static final WholeNumberSet NONE = new WholeNumberSet(List.of());

    /** Every whole number. */
    public static final WholeNumberSet EVERY = ofRuns(WholeNumberRuns.EVERY);

    public WholeNumberSet {
        parts = List.copyOf(parts);
    }

    /** The numbers {@code runs} holds. */
    public static WholeNumberSet ofRuns(WholeNumberRuns runs) {
        List<Part> parts = new ArrayList<>();
        for (WholeNumberRuns.Run each : runs.runs()) {
            parts.add(new Part(each, EVERY_NUMBER));
        }
        return new WholeNumberSet(parts);
    }

    /** The numbers of {@code within}, as far as they go either way. */
    public static WholeNumberSet ofClass(Congruences within) {
        return new WholeNumberSet(List.of(new Part(new WholeNumberRuns.Run(null, null), within)));
    }

    /** Whether {@code number} is one of these. */
    public boolean holds(BigInteger number) {
        return parts.stream().anyMatch(part -> part.holds(number));
    }

    /** Whether no number is one of these. */
    public boolean isNone() {
        return parts.isEmpty();
    }

    /** The numbers both hold: every pair of progressions met. */
    public WholeNumberSet and(WholeNumberSet other) {
        List<Part> both = new ArrayList<>();
        for (Part mine : parts) {
            for (Part theirs : other.parts) {
                Congruences shared = mine.within().meet(theirs.within());
                if (shared == null) {
                    continue;
                }
                BigInteger from = later(mine.run().from(), theirs.run().from());
                BigInteger to = earlier(mine.run().to(), theirs.run().to());
                if (from != null && to != null && from.compareTo(to) > 0) {
                    continue;
                }
                Part part = Part.orNone(new WholeNumberRuns.Run(from, to), shared);
                if (part != null) {
                    both.add(part);
                }
            }
        }
        return new WholeNumberSet(both);
    }

    /** The numbers either holds. */
    public WholeNumberSet or(WholeNumberSet other) {
        List<Part> either = new ArrayList<>(parts);
        either.addAll(other.parts);
        return new WholeNumberSet(either);
    }

    /** The greatest number at or below {@code number}, or null where none is. */
    public BigInteger greatestAtOrBelow(BigInteger number) {
        BigInteger best = null;
        for (Part part : parts) {
            BigInteger at = part.atOrBelow(number);
            if (at != null && (best == null || at.compareTo(best) > 0)) {
                best = at;
            }
        }
        return best;
    }

    /** The least number at or above {@code number}, or null where none is. */
    public BigInteger leastAtOrAbove(BigInteger number) {
        BigInteger best = null;
        for (Part part : parts) {
            BigInteger at = part.atOrAbove(number);
            if (at != null && (best == null || at.compareTo(best) < 0)) {
                best = at;
            }
        }
        return best;
    }

    /** The least number, or null where there is none or no least. */
    public BigInteger least() {
        BigInteger best = null;
        for (Part part : parts) {
            if (part.run().from() == null) {
                return null;
            }
            if (best == null || part.run().from().compareTo(best) < 0) {
                best = part.run().from();
            }
        }
        return best;
    }

    /** The greatest number, or null where there is none or no greatest. */
    public BigInteger greatest() {
        BigInteger best = null;
        for (Part part : parts) {
            if (part.run().to() == null) {
                return null;
            }
            if (best == null || part.run().to().compareTo(best) > 0) {
                best = part.run().to();
            }
        }
        return best;
    }

    /**
     * The values {@code c} of another number for which a number {@code s} of this exists with
     * {@code weightHere·s + weightThere·c + constant = 0} — or null where a weight is nought.
     *
     * <p>What one number leaves of another beside it in an equation: {@code 2·x = c} leaves the
     * even numbers of {@code c} where {@code x} may be any, and {@code x = c} leaves those of
     * {@code x}. Worked out for each progression as a remainder of {@code c}, and the ends of the
     * run it is of carried over, so no number of the sets is listed.
     */
    public WholeNumberSet valuesBeside(BigInteger weightHere, BigInteger weightThere,
                                       BigInteger constant) {
        if (weightHere.signum() == 0 || weightThere.signum() == 0) {
            return null;
        }
        List<Part> out = new ArrayList<>();
        for (Part part : parts) {
            Congruences leaves = Congruences.solving(weightThere,
                    constant.add(weightHere.multiply(part.within().residue())),
                    weightHere.abs().multiply(part.within().modulus()));
            if (leaves == null) {
                continue;
            }
            // weightThere·c = -weightHere·s - constant, for s from the run's least to greatest.
            BigInteger atLeast = part.run().from() == null ? null
                    : weightHere.negate().multiply(part.run().from()).subtract(constant);
            BigInteger atGreatest = part.run().to() == null ? null
                    : weightHere.negate().multiply(part.run().to()).subtract(constant);
            BigInteger smallest = weightHere.signum() > 0 ? atGreatest : atLeast;
            BigInteger largest = weightHere.signum() > 0 ? atLeast : atGreatest;
            BigInteger from;
            BigInteger to;
            if (weightThere.signum() > 0) {
                from = smallest == null ? null : ceilDivided(smallest, weightThere);
                to = largest == null ? null : floorDivided(largest, weightThere);
            } else {
                from = largest == null ? null : ceilDivided(largest, weightThere);
                to = smallest == null ? null : floorDivided(smallest, weightThere);
            }
            if (from != null && to != null && from.compareTo(to) > 0) {
                continue;
            }
            Part found = Part.orNone(new WholeNumberRuns.Run(from, to), leaves);
            if (found != null) {
                out.add(found);
            }
        }
        return new WholeNumberSet(out);
    }

    /**
     * These numbers as runs, or null where some progression is more than a run: one that steps
     * over numbers between its members, and holds more than the one.
     */
    public WholeNumberRuns asRuns() {
        WholeNumberRuns out = WholeNumberRuns.NONE;
        for (Part each : parts) {
            boolean single = each.run().from() != null && each.run().from().equals(each.run().to());
            if (!single && each.within().modulus().compareTo(BigInteger.ONE) > 0) {
                return null;
            }
            out = out.or(WholeNumberRuns.one(each.run().from(), each.run().to()));
        }
        return out;
    }

    /**
     * What building a set may cost, in the progressions it holds.
     *
     * <p>Asked before the progressions are made: the complement of a remainder by a thousand
     * million is as many progressions as remainders, and a set that was built to see whether it
     * fits is the cost the question exists to avoid.
     */
    public interface Budget {

        /** Whether a set of {@code parts} progressions may be built. */
        boolean allows(long parts);
    }

    /**
     * The numbers both hold, or null where a set within {@code budget} cannot hold them: the
     * answer is never a part of the numbers standing for all of them.
     */
    public WholeNumberSet and(WholeNumberSet other, Budget budget) {
        if (!budget.allows((long) parts.size() * other.parts.size())) {
            return null;
        }
        WholeNumberSet met = and(other).simplified();
        return budget.allows(met.parts.size()) ? met : null;
    }

    /** The numbers either holds, or null where a set within {@code budget} cannot hold them. */
    public WholeNumberSet or(WholeNumberSet other, Budget budget) {
        if (!budget.allows((long) parts.size() + other.parts.size())) {
            return null;
        }
        WholeNumberSet joined = or(other).simplified();
        return budget.allows(joined.parts.size()) ? joined : null;
    }

    /**
     * The whole numbers none of these is, or null where a set within {@code budget} cannot hold
     * them.
     *
     * <p>The complement of a progression is the numbers outside its run, and inside the run the
     * other remainders of its divisor, so it costs as many progressions as its divisor is large.
     * That is asked before they are made, and of the complement of each part met in turn.
     */
    public WholeNumberSet complement(Budget budget) {
        WholeNumberSet out = EVERY;
        for (Part part : parts) {
            WholeNumberSet outside = complementOf(part, budget);
            if (outside == null) {
                return null;
            }
            out = out.and(outside, budget);
            if (out == null) {
                return null;
            }
        }
        return out;
    }

    private static WholeNumberSet complementOf(Part part, Budget budget) {
        BigInteger modulus = part.within().modulus();
        BigInteger others = modulus.subtract(BigInteger.ONE);
        if (others.bitLength() > 62 || !budget.allows(others.longValueExact() + 2)) {
            return null;
        }
        List<Part> out = new ArrayList<>();
        if (part.run().from() != null) {
            out.add(new Part(new WholeNumberRuns.Run(null,
                    part.run().from().subtract(BigInteger.ONE)), EVERY_NUMBER));
        }
        if (part.run().to() != null) {
            out.add(new Part(new WholeNumberRuns.Run(part.run().to().add(BigInteger.ONE), null),
                    EVERY_NUMBER));
        }
        for (BigInteger residue = BigInteger.ZERO; residue.compareTo(modulus) < 0;
             residue = residue.add(BigInteger.ONE)) {
            if (residue.equals(part.within().residue())) {
                continue;
            }
            Part other = Part.orNone(part.run(), new Congruences(residue, modulus));
            if (other != null) {
                out.add(other);
            }
        }
        return new WholeNumberSet(out);
    }

    /**
     * The same numbers with no progression held by another and no two of one remainder that touch.
     *
     * <p>Not a normal form: evens and odds are not joined into every number, so two sets holding
     * the same numbers may be spelled differently, and {@code equals} says how they are spelled.
     */
    WholeNumberSet simplified() {
        List<Part> kept = new ArrayList<>();
        for (Part each : parts) {
            if (kept.stream().noneMatch(other -> holdsAll(other, each))) {
                kept.removeIf(other -> holdsAll(each, other));
                kept.add(each);
            }
        }
        boolean joined = true;
        while (joined) {
            joined = false;
            for (int i = 0; i < kept.size() && !joined; i++) {
                for (int j = i + 1; j < kept.size() && !joined; j++) {
                    Part together = joinedIfTouching(kept.get(i), kept.get(j));
                    if (together != null) {
                        kept.remove(j);
                        kept.set(i, together);
                        joined = true;
                    }
                }
            }
        }
        return new WholeNumberSet(kept);
    }

    /** Whether every number of {@code inner} is one of {@code outer}. */
    private static boolean holdsAll(Part outer, Part inner) {
        BigInteger modulus = outer.within().modulus();
        return inner.within().modulus().mod(modulus).signum() == 0
                && inner.within().residue().subtract(outer.within().residue()).mod(modulus)
                        .signum() == 0
                && (outer.run().from() == null || (inner.run().from() != null
                        && inner.run().from().compareTo(outer.run().from()) >= 0))
                && (outer.run().to() == null || (inner.run().to() != null
                        && inner.run().to().compareTo(outer.run().to()) <= 0));
    }

    /** One progression of both, where they are of one remainder and no number between is left
     *  out; else null. */
    private static Part joinedIfTouching(Part one, Part other) {
        if (!one.within().equals(other.within())) {
            return null;
        }
        BigInteger step = one.within().modulus();
        BigInteger oneFrom = one.run().from();
        BigInteger oneTo = one.run().to();
        BigInteger otherFrom = other.run().from();
        BigInteger otherTo = other.run().to();
        boolean otherStartsInTime = otherFrom == null || oneTo == null
                || otherFrom.compareTo(oneTo.add(step)) <= 0;
        boolean oneStartsInTime = oneFrom == null || otherTo == null
                || oneFrom.compareTo(otherTo.add(step)) <= 0;
        if (!otherStartsInTime || !oneStartsInTime) {
            return null;
        }
        return new Part(new WholeNumberRuns.Run(
                oneFrom == null || otherFrom == null ? null : oneFrom.min(otherFrom),
                oneTo == null || otherTo == null ? null : oneTo.max(otherTo)), one.within());
    }

    /**
     * The member nearest {@code target} that is none of {@code excluded}, or null where there is
     * none. Members are walked outward from the target, and no more of them than the excluded
     * values can stand in the way of.
     */
    public BigInteger nearestMember(BigInteger target, Set<BigInteger> excluded) {
        BigInteger above = target;
        BigInteger below = target;
        for (long step = 0; step <= 2L * excluded.size() + 2; step++) {
            BigInteger up = above == null ? null : leastAtOrAbove(above);
            BigInteger down = below == null ? null : greatestAtOrBelow(below);
            if (up == null && down == null) {
                return null;
            }
            boolean takeUp = down == null || (up != null
                    && up.subtract(target).compareTo(target.subtract(down)) <= 0);
            BigInteger pick = takeUp ? up : down;
            if (!excluded.contains(pick)) {
                return pick;
            }
            if (takeUp) {
                above = up.add(BigInteger.ONE);
            } else {
                below = down.subtract(BigInteger.ONE);
            }
        }
        return null;
    }

    private static BigInteger floorDivided(BigInteger number, BigInteger by) {
        BigInteger[] both = number.divideAndRemainder(by);
        return both[1].signum() != 0 && (both[1].signum() != by.signum())
                ? both[0].subtract(BigInteger.ONE) : both[0];
    }

    private static BigInteger ceilDivided(BigInteger number, BigInteger by) {
        BigInteger[] both = number.divideAndRemainder(by);
        return both[1].signum() != 0 && (both[1].signum() == by.signum())
                ? both[0].add(BigInteger.ONE) : both[0];
    }

    private static BigInteger later(BigInteger one, BigInteger other) {
        return one == null ? other : other == null ? one : one.max(other);
    }

    private static BigInteger earlier(BigInteger one, BigInteger other) {
        return one == null ? other : other == null ? one : one.min(other);
    }
}
