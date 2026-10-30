package souther.compiler.numeric;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;

/**
 * A set of numbers held as the runs it is made of, in order, none touching another.
 *
 * <p>A region and not an interval: the numbers a reading says nothing about can lie in several
 * runs with numbers it does say something about between them, and one interval from the first to
 * the last would claim those too. Two runs that overlap, or that meet at a value one of them
 * admits, are one run, so one set of numbers has one spelling.
 *
 * <p>It says which numbers and nothing of how they come out. A run that carries a verdict
 * ({@code holds}) is a different thing, and the verdict is not part of where the numbers are.
 */
public record NumberRegion(List<Run> runs) implements Comparable<NumberRegion> {

    /**
     * One run of the region.
     *
     * @param from the lower end, or null where the run has no least
     * @param to   the upper end, or null where the run has no greatest
     */
    public record Run(ExactCut from, ExactCut to) {

        public Run {
            if (from != null && to != null && (from.at().compareTo(to.at()) > 0
                    || (from.at().compareTo(to.at()) == 0
                            && !(from.inclusive() && to.inclusive())))) {
                throw new IllegalArgumentException("a run holds some number: " + from + " to " + to);
            }
        }

        private boolean reaches(Run next) {
            if (to == null || next.from == null) {
                return true;
            }
            int order = to.at().compareTo(next.from.at());
            return order > 0 || (order == 0 && (to.inclusive() || next.from.inclusive()));
        }

        private Run joinedWith(Run next) {
            return new Run(from, upperOf(to, next.to));
        }

        private static ExactCut upperOf(ExactCut one, ExactCut other) {
            if (one == null || other == null) {
                return null;
            }
            int order = one.at().compareTo(other.at());
            if (order == 0) {
                return one.inclusive() ? one : other;
            }
            return order > 0 ? one : other;
        }

        private static int byLowerEnd(Run one, Run other) {
            if (one.from == null || other.from == null) {
                return Boolean.compare(other.from == null, one.from == null);
            }
            int order = one.from.at().compareTo(other.from.at());
            return order != 0 ? order
                    : Boolean.compare(other.from.inclusive(), one.from.inclusive());
        }

        private static int byUpperEnd(Run one, Run other) {
            if (one.to == null || other.to == null) {
                return Boolean.compare(one.to == null, other.to == null);
            }
            int order = one.to.at().compareTo(other.to.at());
            return order != 0 ? order : Boolean.compare(one.to.inclusive(), other.to.inclusive());
        }
    }

    public NumberRegion {
        runs = normalized(runs);
        if (runs.isEmpty()) {
            throw new IllegalArgumentException("a region of numbers holds some");
        }
    }

    /** The region these runs make together. */
    public static NumberRegion of(List<Run> runs) {
        return new NumberRegion(runs);
    }

    /** This region and {@code other} together. */
    public NumberRegion and(NumberRegion other) {
        List<Run> both = new ArrayList<>(runs);
        both.addAll(other.runs);
        return new NumberRegion(both);
    }

    private static List<Run> normalized(List<Run> runs) {
        List<Run> sorted = new ArrayList<>(runs);
        sorted.sort(Run::byLowerEnd);
        List<Run> out = new ArrayList<>();
        for (Run each : sorted) {
            int last = out.size() - 1;
            if (last >= 0 && out.get(last).reaches(each)) {
                out.set(last, out.get(last).joinedWith(each));
            } else {
                out.add(each);
            }
        }
        return List.copyOf(out);
    }

    /** In an order that is nobody's, equal only for equal regions: run by run, the lower end and
     *  then the upper. */
    @Override
    public int compareTo(NumberRegion other) {
        Comparator<Run> byRun = Run::byLowerEnd;
        byRun = byRun.thenComparing(Run::byUpperEnd);
        for (int i = 0; i < Math.min(runs.size(), other.runs.size()); i++) {
            int order = byRun.compare(runs.get(i), other.runs.get(i));
            if (order != 0) {
                return order;
            }
        }
        return Integer.compare(runs.size(), other.runs.size());
    }
}
