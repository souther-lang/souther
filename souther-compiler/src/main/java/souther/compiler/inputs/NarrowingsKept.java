package souther.compiler.inputs;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.BiFunction;

/**
 * The regions a base region was narrowed to by the leading steps of a list, kept so that a longer
 * list starting with the same steps is narrowed from the longest of them rather than from the base.
 *
 * <p>Narrowing is a left fold: the region after {@code n} steps is the base with each of them taken
 * in, in order, and nothing else. The ways a search is asked about grow by one condition at a time
 * as the cases of a line are chosen, so the list of steps a way takes in is the list of the way
 * before it with a few more, and each of those was folded from the base again.
 *
 * <p>Kept at every {@link #EVERY}th step and at the end of each list, and no more than {@link
 * #HELD} of them, the least recently used going first. The ways are asked depth first, so the way
 * a longer one extends was asked a moment ago; a few steps of the fold are redone from the nearest
 * kept step, and what is held does not grow with the number of ways asked.
 *
 * <p>A list is looked up at its own length and at each multiple of {@link #EVERY} below it, and not
 * at every length: a key is the whole leading run, so asking at every length hashes the run once
 * per length, which costs more than the steps it saves.
 *
 * <p>A step is part of the key by its equality, which is everything a step says of the region it
 * narrows, so a region lent is the region the fold would have made.
 *
 * <p>The key is the steps alone, so what is kept is the answer for one base and one narrowing. The
 * base is the region that hands out this object as its own {@link SearchRegion#narrowingsKept()},
 * and a base that does not is folded from itself without reading or writing what is kept. The
 * narrowing is the one function every caller of a base uses.
 */
public final class NarrowingsKept {

    /** Nothing kept: every list is folded from the base. */
    static final NarrowingsKept NONE = new NarrowingsKept(0);

    private static final int EVERY = 4;
    private static final int HELD = 64;

    private final Map<List<?>, SearchRegion> kept;

    NarrowingsKept() {
        this(HELD);
    }

    private NarrowingsKept(int held) {
        this.kept = held == 0 ? null : new LinkedHashMap<>(16, 0.75f, true) {
            @Override
            protected boolean removeEldestEntry(Map.Entry<List<?>, SearchRegion> eldest) {
                return size() > held;
            }
        };
    }

    /**
     * {@code base} with every step of {@code steps} taken in by {@code narrowing}, in order.
     */
    public <S> SearchRegion through(SearchRegion base, List<S> steps,
                                    BiFunction<S, SearchRegion, SearchRegion> narrowing) {
        int n = steps.size();
        SearchRegion region = base;
        int from = 0;
        boolean ownBase = kept != null && base.narrowingsKept() == this;
        if (ownBase) {
            synchronized (kept) {
                for (int at = n; at > 0; at = (at - 1) / EVERY * EVERY) {
                    SearchRegion had = kept.get(steps.subList(0, at));
                    if (had != null) {
                        region = had;
                        from = at;
                        break;
                    }
                }
            }
        }
        for (int at = from; at < n; at++) {
            region = narrowing.apply(steps.get(at), region);
            int done = at + 1;
            if (ownBase && (done == n || done % EVERY == 0)) {
                List<S> key = List.copyOf(steps.subList(0, done));
                synchronized (kept) {
                    kept.put(key, region);                }
            }
        }
        return region;
    }
}
