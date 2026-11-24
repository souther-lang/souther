package souther.compiler.partition;

import souther.compiler.inputs.Denotation;
import souther.compiler.inputs.ReadMeaning;
import souther.compiler.meaning.KeptWays;

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
 *
 * <p>What the truths state is held here, and what decides the ways is {@link KeptWays}, which is
 * all a statement over the ways keeps of them.
 */
final class WaysOfKeeping {

    private final List<Denotation> truths = new ArrayList<>();
    private final KeptWays kept;

    WaysOfKeeping(List<ReadMeaning.Occurrence> occurrences) {
        List<List<KeptWays.Keep>> keptBy = new ArrayList<>();
        for (ReadMeaning.Occurrence occurrence : occurrences) {
            List<KeptWays.Keep> keeps = new ArrayList<>();
            for (ReadMeaning.Occurrence.Kept each : occurrence.keptWhere()) {
                ReadMeaning.Occurrence.Kept.ATruth truth = truthOf(each);
                int index = truths.indexOf(truth.truth());
                if (index < 0) {
                    index = truths.size();
                    truths.add(truth.truth());
                }
                keeps.add(new KeptWays.Keep(index, truth.holds()));
            }
            keptBy.add(keeps);
        }
        kept = new KeptWays(keptBy, truths.size());
    }

    /** Whether every truth an occurrence is kept by is one ({@code false} where one is an arm of a
     *  choice, which this does not decide). */
    static boolean allTruths(List<ReadMeaning.Occurrence> occurrences) {
        return occurrences.stream().flatMap(one -> one.keptWhere().stream())
                .allMatch(kept -> kept instanceof ReadMeaning.Occurrence.Kept.ATruth);
    }

    /** What decides the ways. */
    KeptWays kept() {
        return kept;
    }

    /** The occurrences and the truths that keep them, as they are told apart by. */
    String spelled() {
        return kept.spelled();
    }

    int truthCount() {
        return truths.size();
    }

    Denotation truth(int index) {
        return truths.get(index);
    }

    /** The decisions of no truth yet. */
    Boolean[] undecided() {
        return kept.undecided();
    }

    /**
     * The first truth some occurrence is handed to and that is not decided yet, given what is
     * decided — or -1 where there is none, and the way is a leaf.
     */
    int nextEvaluated(Boolean[] decided) {
        return kept.nextEvaluated(decided);
    }

    /** Whether occurrence {@code i} is there at a leaf, every truth it is kept by decided as it
     *  was kept. */
    boolean isThere(int i, Boolean[] decided) {
        return kept.isThere(i, decided);
    }

    /** How many readings the tree makes in all, or {@code limit} where it makes that many or
     *  more ({@link KeptWays#work}). */
    long work(Boolean[] decided, long limit, boolean readsTheElements) {
        return kept.work(decided, limit, readsTheElements);
    }

    private static ReadMeaning.Occurrence.Kept.ATruth truthOf(ReadMeaning.Occurrence.Kept kept) {
        return (ReadMeaning.Occurrence.Kept.ATruth) kept;
    }
}
