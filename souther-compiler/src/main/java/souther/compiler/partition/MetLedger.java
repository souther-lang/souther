package souther.compiler.partition;

import java.util.AbstractList;
import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;

/**
 * The parts a reading has met, in the order it met them, and which of them are still met.
 *
 * <p>A rule that is set aside takes back out of the list what it met ({@link RuleChoice}), by
 * clearing a range of it. A reading kept to be taken again leaves its parts here when it is made,
 * and a rule set aside later may have taken them: it is the ledger that tells, by the part itself,
 * which parts of a reading are met and meets the rest again.
 *
 * @param <M> the part met
 */
final class MetLedger<M> extends AbstractList<M> {

    private final List<M> parts = new ArrayList<>();
    private final Map<M, Integer> counts = new IdentityHashMap<>();

    @Override
    public M get(int at) {
        return parts.get(at);
    }

    @Override
    public int size() {
        return parts.size();
    }

    @Override
    public void add(int at, M part) {
        parts.add(at, part);
        counts.merge(part, 1, Integer::sum);
        modCount++;
    }

    @Override
    public M remove(int at) {
        M gone = parts.remove(at);
        forget(gone);
        modCount++;
        return gone;
    }

    @Override
    protected void removeRange(int from, int to) {
        List<M> gone = parts.subList(from, to);
        for (M each : gone) {
            forget(each);
        }
        gone.clear();
        modCount++;
    }

    private void forget(M part) {
        counts.merge(part, -1, (had, _) -> had == 1 ? null : had - 1);
    }

    /**
     * Meets again each of {@code some} that is not met, at the end, in the order it was met.
     *
     * <p>The parts of a reading that a rule set aside took back are the parts the reading would
     * meet if it were made again here. A part still met is left where it was met: it is the very
     * part, and met once.
     */
    void meetAgain(List<? extends M> some) {
        for (M each : some) {
            if (!counts.containsKey(each)) {
                add(each);
            }
        }
    }
}
