package souther.compiler.numeric;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

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

    private static BigInteger later(BigInteger one, BigInteger other) {
        return one == null ? other : other == null ? one : one.max(other);
    }

    private static BigInteger earlier(BigInteger one, BigInteger other) {
        return one == null ? other : other == null ? one : one.min(other);
    }
}
