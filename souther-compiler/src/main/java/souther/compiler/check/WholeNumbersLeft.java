package souther.compiler.check;

import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Rel;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;

/**
 * The whole numbers a statement about one number leaves it, as the runs between the lines the
 * statement draws.
 *
 * <p>Exact both ways: a number is in a run exactly where the statement holds of it. That is what
 * lets a choice between comparisons of one number be held as the numbers it leaves rather than as a
 * choice — {@code r < 4 || r == 6} over a remainder by seven is the five numbers it leaves, and
 * nothing a range around them would add.
 *
 * <p>The runs are in order, apart and not touching: two runs one apart are one run. So two of these
 * leaving the same numbers are equal.
 */
record WholeNumbersLeft(List<Run> runs) {

    /**
     * From {@code from} to {@code to}, both held, or as far as the numbers go where an end is null.
     */
    record Run(BigInteger from, BigInteger to) {

        Run {
            if (from != null && to != null && from.compareTo(to) > 0) {
                throw new IllegalArgumentException("a run holds a number: " + from + ".." + to);
            }
        }

        /** How many numbers it holds, or null where it has no end one way. */
        BigInteger count() {
            return from == null || to == null ? null : to.subtract(from).add(BigInteger.ONE);
        }
    }

    /** Every whole number. */
    static final WholeNumbersLeft EVERY = new WholeNumbersLeft(List.of(new Run(null, null)));

    /** No number at all. */
    static final WholeNumbersLeft NONE = new WholeNumbersLeft(List.of());

    WholeNumbersLeft {
        runs = List.copyOf(runs);
        for (int i = 1; i < runs.size(); i++) {
            Run before = runs.get(i - 1);
            Run after = runs.get(i);
            if (before.to() == null || after.from() == null
                    || before.to().add(BigInteger.ONE).compareTo(after.from()) >= 0) {
                throw new IllegalArgumentException("runs in order, apart and not touching: " + runs);
            }
        }
    }

    /**
     * The whole numbers that stand {@code rel} to {@code at}, or null where the whole numbers
     * either side of {@code at} are past what the exact arithmetic holds.
     */
    static WholeNumbersLeft standing(Rel rel, ExactRatio at) {
        if (!(at.floor() instanceof ExactAnswer.Held<BigInteger>(BigInteger below))
                || !(at.ceiling() instanceof ExactAnswer.Held<BigInteger>(BigInteger above))) {
            return null;
        }
        boolean whole = below.equals(above);
        return switch (rel) {
            case GE -> one(above, null);
            case GT -> one(below.add(BigInteger.ONE), null);
            case LE -> one(null, below);
            case LT -> one(null, above.subtract(BigInteger.ONE));
            case EQ -> whole ? one(below, below) : NONE;
            case NE -> whole ? one(below, below).others() : EVERY;
        };
    }

    /** The numbers from {@code from} to {@code to}, either end null for no end, and none where the
     *  first is past the second. */
    static WholeNumbersLeft one(BigInteger from, BigInteger to) {
        return from != null && to != null && from.compareTo(to) > 0 ? NONE
                : new WholeNumbersLeft(List.of(new Run(from, to)));
    }

    /** The numbers this leaves and {@code other} leaves too. */
    WholeNumbersLeft and(WholeNumbersLeft other) {
        List<Run> out = new ArrayList<>();
        for (Run mine : runs) {
            for (Run theirs : other.runs) {
                BigInteger from = mine.from() == null ? theirs.from()
                        : theirs.from() == null ? mine.from() : mine.from().max(theirs.from());
                BigInteger to = mine.to() == null ? theirs.to()
                        : theirs.to() == null ? mine.to() : mine.to().min(theirs.to());
                if (from == null || to == null || from.compareTo(to) <= 0) {
                    out.add(new Run(from, to));
                }
            }
        }
        return joined(out);
    }

    /** The numbers this leaves or {@code other} leaves. */
    WholeNumbersLeft or(WholeNumbersLeft other) {
        List<Run> all = new ArrayList<>(runs);
        all.addAll(other.runs);
        return joined(all);
    }

    /** The numbers this does not leave. */
    WholeNumbersLeft others() {
        List<Run> out = new ArrayList<>();
        BigInteger next = null;
        boolean fromTheStart = true;
        for (Run run : runs) {
            if (run.from() != null && (fromTheStart || next.compareTo(run.from()) < 0)) {
                out.add(new Run(fromTheStart ? null : next, run.from().subtract(BigInteger.ONE)));
            }
            if (run.to() == null) {
                return new WholeNumbersLeft(out);
            }
            next = run.to().add(BigInteger.ONE);
            fromTheStart = false;
        }
        out.add(new Run(fromTheStart ? null : next, null));
        return new WholeNumbersLeft(out);
    }

    /** How many numbers this leaves, or null where they have no end. */
    BigInteger count() {
        BigInteger all = BigInteger.ZERO;
        for (Run run : runs) {
            BigInteger here = run.count();
            if (here == null) {
                return null;
            }
            all = all.add(here);
        }
        return all;
    }

    /** Each number this leaves, in order; asked only of a set {@link #count} says has an end. */
    List<BigInteger> each() {
        List<BigInteger> out = new ArrayList<>();
        for (Run run : runs) {
            for (BigInteger n = run.from(); n.compareTo(run.to()) <= 0; n = n.add(BigInteger.ONE)) {
                out.add(n);
            }
        }
        return out;
    }

    /** {@code runs} in order, with those that overlap or touch made one. */
    private static WholeNumbersLeft joined(List<Run> runs) {
        List<Run> sorted = new ArrayList<>(runs);
        sorted.sort(Comparator.comparing(Run::from,
                Comparator.nullsFirst(Comparator.<BigInteger>naturalOrder())));
        List<Run> out = new ArrayList<>();
        for (Run run : sorted) {
            if (!out.isEmpty()) {
                Run last = out.getLast();
                if (last.to() == null) {
                    break;
                }
                if (run.from() == null
                        || last.to().add(BigInteger.ONE).compareTo(run.from()) >= 0) {
                    BigInteger to = run.to() == null ? null : run.to().max(last.to());
                    out.set(out.size() - 1, new Run(last.from(), to));
                    continue;
                }
            }
            out.add(run);
        }
        return new WholeNumbersLeft(out);
    }
}
