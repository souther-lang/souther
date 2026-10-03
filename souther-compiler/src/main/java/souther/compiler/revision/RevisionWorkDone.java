package souther.compiler.revision;

import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.SequencedSet;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicLong;

/**
 * What {@link RevisionKnowledge#done} keeps about the work it does: how many of each kind it worked
 * out, and which it is working out now.
 *
 * <p>Its own class because an interface has no private state, and a count anybody could reset is
 * not one a test can hold a reader to.
 */
final class RevisionWorkDone {

    private static final Map<Class<?>, AtomicLong> DONE = new ConcurrentHashMap<>();

    /**
     * The work under way on this thread, by the knowledge it is being done for, in the order it
     * was entered.
     *
     * <p>By the knowledge's identity, because what makes a piece of work borrow itself is asking
     * the same knowledge for it while it is being done for that knowledge; the same work done for
     * another revision is another piece of work. And on the thread, because the knowledge is
     * confined to the thread its store's walk is on.
     */
    private static final ThreadLocal<Map<RevisionKnowledge, SequencedSet<RevisionWork<?>>>>
            UNDER_WAY = ThreadLocal.withInitial(IdentityHashMap::new);

    static void count(Class<?> kind) {
        DONE.computeIfAbsent(kind, _ -> new AtomicLong()).incrementAndGet();
    }

    static long of(Class<?> kind) {
        AtomicLong done = DONE.get(kind);
        return done == null ? 0 : done.get();
    }

    /**
     * Says {@code work} is being done for {@code revision}, refusing it where it already is.
     *
     * <p>Work that borrows itself, however many pieces of work away, would be done again inside
     * itself until the stack ran out, with nothing kept on the way. Refused at the second entry
     * instead, with the way round it named.
     */
    static void entering(RevisionKnowledge revision, RevisionWork<?> work) {
        SequencedSet<RevisionWork<?>> path =
                UNDER_WAY.get().computeIfAbsent(revision, _ -> new LinkedHashSet<>());
        if (!path.add(work)) {
            StringBuilder round = new StringBuilder();
            for (RevisionWork<?> each : path) {
                round.append(each).append(" -> ");
            }
            throw new IllegalStateException(
                    "revision work borrows itself: " + round.append(work));
        }
    }

    /** Says {@code work} is no longer being done for {@code revision}, whatever it came to. */
    static void leaving(RevisionKnowledge revision, RevisionWork<?> work) {
        Map<RevisionKnowledge, SequencedSet<RevisionWork<?>>> underWay = UNDER_WAY.get();
        SequencedSet<RevisionWork<?>> path = underWay.get(revision);
        if (path != null) {
            path.remove(work);
            if (path.isEmpty()) {
                underWay.remove(revision);
            }
        }
    }

    private RevisionWorkDone() {}
}
