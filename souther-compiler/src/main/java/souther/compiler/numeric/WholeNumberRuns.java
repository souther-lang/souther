package souther.compiler.numeric;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;

/**
 * A set of whole numbers, as the runs it holds.
 *
 * <p>What a statement about one whole number leaves it: the runs between the lines its comparisons
 * draw. Exact both ways — a number is in a run exactly where the statement holds of it — and held
 * by its ends, so a run of a thousand million numbers is two numbers here. That is what lets a
 * choice between comparisons of one number be held as the numbers it leaves rather than as a
 * choice: {@code r < 4 || r == 6} over a remainder by seven is the runs nought to three and six,
 * and over a remainder by a thousand million it is two runs still.
 *
 * <p>Every operation here works on the runs and none on the numbers in them, so what each costs is
 * how many runs there are. Each comparison adds at most two ends, so a statement of so many
 * comparisons leaves at most one run more than that many.
 *
 * <p>The runs are in order, apart and not touching: two runs one apart are one run. So two of these
 * holding the same numbers are equal.
 *
 * @param runs the runs, in order
 */
public record WholeNumberRuns(List<Run> runs) {

    /**
     * From {@code from} to {@code to}, both held, or as far as the numbers go where an end is null.
     */
    public record Run(BigInteger from, BigInteger to) {

        public Run {
            if (from != null && to != null && from.compareTo(to) > 0) {
                throw new IllegalArgumentException("a run holds a number: " + from + ".." + to);
            }
        }

        /** How many numbers it holds, or null where it has no end one way. */
        public BigInteger count() {
            return from == null || to == null ? null : to.subtract(from).add(BigInteger.ONE);
        }

        /** Whether it holds {@code number}. */
        public boolean holds(BigInteger number) {
            return (from == null || from.compareTo(number) <= 0)
                    && (to == null || to.compareTo(number) >= 0);
        }

        /** Whether it holds one number and no other. */
        public boolean isOneNumber() {
            return from != null && from.equals(to);
        }
    }

    /** Every whole number. */
    public static final WholeNumberRuns EVERY = new WholeNumberRuns(List.of(new Run(null, null)));

    /** No number at all. */
    public static final WholeNumberRuns NONE = new WholeNumberRuns(List.of());

    public WholeNumberRuns {
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
    public static WholeNumberRuns standing(Rel rel, ExactRatio at) {
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
    public static WholeNumberRuns one(BigInteger from, BigInteger to) {
        return from != null && to != null && from.compareTo(to) > 0 ? NONE
                : new WholeNumberRuns(List.of(new Run(from, to)));
    }

    /**
     * The whole numbers from {@code low} to {@code high}, either of them null for no end.
     *
     * <p>An end at no number counts as none, which holds every number the end would have kept out:
     * what this is asked for is where a number may be, and a range read wider than it is leaves out
     * no number that is in it.
     */
    public static WholeNumberRuns between(Endpoint low, Endpoint high) {
        return one(lowestAt(low), highestAt(high));
    }

    /** The least whole number at or past {@code end}, or null for none to name. */
    private static BigInteger lowestAt(Endpoint end) {
        if (end == null || !(end.at() instanceof Count count)) {
            return null;
        }
        if (end.inclusive()) {
            return count.exactly().ceiling() instanceof ExactAnswer.Held<BigInteger>(var up)
                    ? up : null;
        }
        return count.exactly().floor() instanceof ExactAnswer.Held<BigInteger>(var down)
                ? down.add(BigInteger.ONE) : null;
    }

    /** The greatest whole number at or before {@code end}, the same way round. */
    private static BigInteger highestAt(Endpoint end) {
        if (end == null || !(end.at() instanceof Count count)) {
            return null;
        }
        if (end.inclusive()) {
            return count.exactly().floor() instanceof ExactAnswer.Held<BigInteger>(var down)
                    ? down : null;
        }
        return count.exactly().ceiling() instanceof ExactAnswer.Held<BigInteger>(var up)
                ? up.subtract(BigInteger.ONE) : null;
    }

    /** These numbers, each as a run of its own. */
    public static WholeNumberRuns of(List<BigInteger> numbers) {
        List<Run> each = new ArrayList<>();
        numbers.forEach(number -> each.add(new Run(number, number)));
        return joined(each);
    }

    /** The numbers this holds and {@code other} holds too. */
    public WholeNumberRuns and(WholeNumberRuns other) {
        // Both in order, so each run here is met only with the runs there it can reach.
        List<Run> out = new ArrayList<>();
        int i = 0;
        int j = 0;
        while (i < runs.size() && j < other.runs.size()) {
            Run mine = runs.get(i);
            Run theirs = other.runs.get(j);
            BigInteger from = later(mine.from(), theirs.from());
            BigInteger to = earlier(mine.to(), theirs.to());
            if (from == null || to == null || from.compareTo(to) <= 0) {
                out.add(new Run(from, to));
            }
            if (endsFirst(mine, theirs)) {
                i++;
            } else {
                j++;
            }
        }
        return new WholeNumberRuns(out);
    }

    /** The numbers this holds or {@code other} holds. */
    public WholeNumberRuns or(WholeNumberRuns other) {
        List<Run> all = new ArrayList<>(runs);
        all.addAll(other.runs);
        return joined(all);
    }

    /** The numbers this does not hold. */
    public WholeNumberRuns others() {
        List<Run> out = new ArrayList<>();
        BigInteger next = null;
        boolean fromTheStart = true;
        for (Run run : runs) {
            if (run.from() != null && (fromTheStart || next.compareTo(run.from()) < 0)) {
                out.add(new Run(fromTheStart ? null : next, run.from().subtract(BigInteger.ONE)));
            }
            if (run.to() == null) {
                return new WholeNumberRuns(out);
            }
            next = run.to().add(BigInteger.ONE);
            fromTheStart = false;
        }
        out.add(new Run(fromTheStart ? null : next, null));
        return new WholeNumberRuns(out);
    }

    /** Whether this holds {@code number}. */
    public boolean holds(BigInteger number) {
        return runs.stream().anyMatch(run -> run.holds(number));
    }

    /** Whether this holds no number. */
    public boolean isNone() {
        return runs.isEmpty();
    }

    /** Whether this holds every number. */
    public boolean isEvery() {
        return runs.size() == 1 && runs.getFirst().from() == null && runs.getFirst().to() == null;
    }

    /** Whether every run holds one number, so the numbers are as many as the runs. */
    public boolean isNumbersApart() {
        return runs.stream().allMatch(Run::isOneNumber);
    }

    /** How many numbers this holds, or null where they have no end. */
    public BigInteger count() {
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

    /** {@code runs} in order, with those that overlap or touch made one. */
    private static WholeNumberRuns joined(List<Run> runs) {
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
        return new WholeNumberRuns(out);
    }

    /** The later of two lower ends, null being no end. */
    private static BigInteger later(BigInteger one, BigInteger other) {
        return one == null ? other : other == null ? one : one.max(other);
    }

    /** The earlier of two upper ends, null being no end. */
    private static BigInteger earlier(BigInteger one, BigInteger other) {
        return one == null ? other : other == null ? one : one.min(other);
    }

    /** Whether {@code mine} stops no later than {@code theirs}. */
    private static boolean endsFirst(Run mine, Run theirs) {
        return mine.to() != null && (theirs.to() == null || mine.to().compareTo(theirs.to()) <= 0);
    }
}
