package souther.compiler.partition;

import souther.compiler.inputs.Denotation;
import souther.compiler.inputs.ReadMeaning;

import java.util.ArrayList;
import java.util.List;

/**
 * The ways the elements of a container written out are kept: each truth that keeps one decided
 * once, and a truth decided only where it is evaluated.
 *
 * <p>An occurrence is kept by truths in the order they were decided, the innermost filter's first
 * ({@link ReadMeaning.Occurrence#keptWhere}). A later truth is the step of a filter that is handed
 * the element only where the earlier ones kept it, so where an earlier one comes out the other way
 * the later one is not evaluated at all: it states nothing there, and whatever it would stop on is
 * no stop of that way. The ways are therefore a tree in which a truth is a node only below the
 * decisions that let an occurrence reach it, and not every combination of truths.
 *
 * <p>The order the truths are evaluated in, which is the order of the fold a filter is written as,
 * is not what the tree carries. A way is a run that gets to the comparison, so every truth it
 * evaluated came to an answer; the truths evaluated are those the decisions reach, whichever came
 * first. A run that stops in a step is no way of reading a value, and is the business of whoever
 * reads what stops a run.
 *
 * <p>One truth shared by occurrences (an element kept by the same outer filter after several inner
 * ones) is one truth, decided once.
 */
final class WaysOfKeeping {

    private final List<ReadMeaning.Occurrence> occurrences;
    private final List<Denotation> truths = new ArrayList<>();
    /** For each occurrence, the index in {@link #truths} of each truth it is kept by. */
    private final int[][] keptBy;

    WaysOfKeeping(List<ReadMeaning.Occurrence> occurrences) {
        this.occurrences = List.copyOf(occurrences);
        keptBy = new int[this.occurrences.size()][];
        for (int i = 0; i < keptBy.length; i++) {
            List<ReadMeaning.Occurrence.Kept> kept = this.occurrences.get(i).keptWhere();
            keptBy[i] = new int[kept.size()];
            for (int j = 0; j < keptBy[i].length; j++) {
                Denotation truth = truthOf(kept.get(j)).truth();
                int index = truths.indexOf(truth);
                if (index < 0) {
                    index = truths.size();
                    truths.add(truth);
                }
                keptBy[i][j] = index;
            }
        }
    }

    /** Whether every truth an occurrence is kept by is one ({@code false} where one is an arm of a
     *  choice, which this does not decide). */
    static boolean allTruths(List<ReadMeaning.Occurrence> occurrences) {
        return occurrences.stream().flatMap(one -> one.keptWhere().stream())
                .allMatch(kept -> kept instanceof ReadMeaning.Occurrence.Kept.ATruth);
    }

    int truthCount() {
        return truths.size();
    }

    Denotation truth(int index) {
        return truths.get(index);
    }

    /** The decisions of no truth yet. */
    Boolean[] undecided() {
        return new Boolean[truths.size()];
    }

    /**
     * The first truth some occurrence is handed to and that is not decided yet, given what is
     * decided — or -1 where there is none, and the way is a leaf.
     */
    int nextEvaluated(Boolean[] decided) {
        int next = -1;
        for (int i = 0; i < keptBy.length; i++) {
            for (int j = 0; j < keptBy[i].length; j++) {
                int truth = keptBy[i][j];
                if (decided[truth] == null) {
                    if (next < 0 || truth < next) {
                        next = truth;
                    }
                    break;
                }
                if (decided[truth] != truthOf(occurrences.get(i).keptWhere().get(j)).holds()) {
                    break;
                }
            }
        }
        return next;
    }

    /** Whether occurrence {@code i} is there at a leaf, every truth it is kept by decided as it
     *  was kept. */
    boolean isThere(int i, Boolean[] decided) {
        for (int j = 0; j < keptBy[i].length; j++) {
            if (decided[keptBy[i][j]] != truthOf(occurrences.get(i).keptWhere().get(j)).holds()) {
                return false;
            }
        }
        return true;
    }

    /**
     * How many elements the tree reads in all, or {@code limit} where it reads that many or more:
     * at each leaf the elements that are there, and one for a leaf that has none.
     *
     * <p>The reading a leaf makes is one of each element there, as the sum of the elements of a
     * container that is not kept by anything is. Counted only to {@code limit}, because what a
     * caller asks is whether the work is within a budget, and a tree of independent truths has as
     * many leaves as there are combinations of them. The truths {@code decided} already are not
     * split again.
     */
    long work(Boolean[] decided, long limit) {
        int next = nextEvaluated(decided);
        if (next < 0) {
            long there = 0;
            for (int i = 0; i < keptBy.length; i++) {
                there += isThere(i, decided) ? 1 : 0;
            }
            return Math.min(limit, Math.max(1, there));
        }
        long total = 0;
        for (boolean holds : new boolean[] {true, false}) {
            decided[next] = holds;
            total += work(decided, limit - total);
            decided[next] = null;
            if (total >= limit) {
                return limit;
            }
        }
        return total;
    }

    private static ReadMeaning.Occurrence.Kept.ATruth truthOf(ReadMeaning.Occurrence.Kept kept) {
        return (ReadMeaning.Occurrence.Kept.ATruth) kept;
    }
}
