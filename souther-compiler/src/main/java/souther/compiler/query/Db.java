package souther.compiler.query;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The store a compilation's questions are asked of: it answers a {@link Key} by running it once,
 * keeps the answer, and hands the same answer to everyone who asks again.
 *
 * <p>It also watches. While a key is being answered, every key it asks is recorded against it, so
 * afterwards the graph knows what each answer was built from. That is what makes a question
 * depending on itself visible at the moment it happens rather than as a stack overflow, and it is
 * what lets an edit be absorbed: change a source, and the only answers recomputed are the ones that
 * read something that changed.
 *
 * <p>Recomputing is not the same as changing. An answer that comes out equal to the one it replaces
 * leaves everything that read it alone — which is what keeps an edit local. Retyping a helper's body
 * changes that module's classes; it does not change what the module declares, so nothing that
 * imports it is looked at again.
 *
 * <p>One store is one workspace over time, not one compile. It is not thread-safe and does not need
 * to be: the work inside a compile is a graph walk, not a set of independent jobs.
 */
public final class Db {

    /**
     * What is known about one key.
     *
     * @param answer the answer as of {@code verifiedAt}
     * @param verifiedAt the revision this answer was last known to be current at
     * @param changedAt the revision the answer last came out different at
     * @param reads what answering it read, in the order it read them
     */
    private record Memo(Answer<?> answer, long verifiedAt, long changedAt, Set<Key<?>> reads) {

        Memo verifiedAt(long revision) {
            return new Memo(answer, revision, changedAt, reads);
        }
    }

    /** Bumped by every input that is given a value it did not already have. */
    private long revision;

    private final Map<Key<?>, Memo> memos = new HashMap<>();
    /** The keys being answered right now, outermost first — the chain a cycle is found on. */
    private final Set<Key<?>> inProgress = new LinkedHashSet<>();
    /** The reads of each in-progress key, innermost frame last. */
    private final Deque<Set<Key<?>>> frames = new ArrayDeque<>();
    /**
     * Keys whose current answer was reached through a cycle. A cyclic answer depends on where the
     * cycle was entered, so keeping it would make one caller's answer depend on whether another
     * asked first; the whole chain in flight when the cycle was found is discarded instead. Cycles
     * are the compiler reporting on a source that names itself, so recomputing them costs nothing
     * that matters.
     */
    private final Set<Key<?>> throughCycle = new HashSet<>();
    /** Every key that has ever reported something, in the order it first did — the order reports
     * are read back in. */
    private final List<Key<?>> spoke = new ArrayList<>();
    private final Set<Key<?>> hasSpoken = new HashSet<>();

    /**
     * Gives an input its value. An input set to what it already held changes nothing, so a caller
     * may hand over a whole workspace on every keystroke. Returns this store, so a compilation can
     * be set up in one expression.
     */
    public <T> Db set(Input<T> key, T value) {
        Answer<T> now = Answer.of(value);
        Memo known = memos.get(key);
        if (known != null && known.answer().equals(now)) {
            return this;
        }
        revision++;
        memos.put(key, new Memo(now, revision, revision, Set.of()));
        return this;
    }

    /** Answers {@code key}, computing it if nothing kept from before still holds. */
    @SuppressWarnings("unchecked")
    public <T> Answer<T> ask(Key<T> key) {
        recordRead(key);
        Memo memo = memos.get(key);
        if (memo != null && memo.verifiedAt() == revision) {
            return (Answer<T>) memo.answer();
        }
        if (inProgress.contains(key)) {
            // Everything in flight has now seen an answer that depends on where it was entered.
            throughCycle.addAll(inProgress);
            return key.onCycle(List.copyOf(inProgress));
        }
        if (memo != null && stillHolds(memo)) {
            memos.put(key, memo.verifiedAt(revision));
            return (Answer<T>) memo.answer();
        }
        inProgress.add(key);
        frames.push(new LinkedHashSet<>());
        Answer<T> answer;
        Set<Key<?>> read;
        try {
            answer = key.compute(this);
        } finally {
            // In the order they were read, so a caller walking the graph for reports meets them in
            // the order the work happened. An unordered copy here makes the first error a module
            // reports depend on hash order.
            read = Collections.unmodifiableSet(frames.pop());
            inProgress.remove(key);
        }
        if (!throughCycle.remove(key)) {
            long changedAt = memo != null && memo.answer().equals(answer)
                    ? memo.changedAt() : revision;
            memos.put(key, new Memo(answer, revision, changedAt, read));
        }
        if (!answer.reports().isEmpty() && hasSpoken.add(key)) {
            spoke.add(key);
        }
        return answer;
    }

    /**
     * Whether {@code memo}'s answer can be kept: everything it read still answers what it did when
     * this answer was made. Asking each of them is what settles that, and each of those may settle
     * the same way without running anything.
     */
    private boolean stillHolds(Memo memo) {
        // Verification is not a read: a key being checked is not a dependency of whoever happened to
        // ask at the moment it was checked.
        frames.push(new LinkedHashSet<>());
        try {
            for (Key<?> read : memo.reads()) {
                ask(read);
                Memo dependency = memos.get(read);
                if (dependency == null || dependency.changedAt() > memo.verifiedAt()) {
                    return false;
                }
            }
        } finally {
            frames.pop();
        }
        return true;
    }

    /**
     * Everything the answers this store now holds have to report, in the order the keys first
     * reported. A key whose answer has since been recomputed contributes what it says now, so a
     * problem that was fixed is not still listed.
     */
    public List<Found> allReports() {
        List<Found> found = new ArrayList<>();
        for (Key<?> key : spoke) {
            Memo memo = memos.get(key);
            if (memo == null) {
                continue;
            }
            for (Report report : memo.answer().reports()) {
                found.add(new Found(key.module(), key.sourceId(), report));
            }
        }
        return found;
    }

    /** What {@code key} read while it was answered, empty if it has not been asked. */
    public Set<Key<?>> dependenciesOf(Key<?> key) {
        Memo memo = memos.get(key);
        return memo == null ? Set.of() : memo.reads();
    }

    /** Whether {@code key}'s answer is being kept — it has been asked, and was not reached through
     * a cycle. */
    public boolean isComputed(Key<?> key) {
        return memos.containsKey(key);
    }

    /** A report, the module it is about, and the source it names — either of which may be null. */
    public record Found(String module, String sourceId, Report report) {}

    /**
     * Everything reported while answering {@code root}, and by everything answering it needed.
     * Deepest first — a module's own errors come before those of a module that read it — so a
     * caller that stops at the first error stops at the same one the passes used to raise.
     */
    public List<Found> reportsUnder(Key<?> root) {
        List<Found> found = new ArrayList<>();
        gather(root, new HashSet<>(), found);
        return found;
    }

    private void gather(Key<?> key, Set<Key<?>> seen, List<Found> found) {
        if (!seen.add(key)) {
            return;
        }
        Memo memo = memos.get(key);
        if (memo == null) {
            return;
        }
        for (Key<?> read : memo.reads()) {
            gather(read, seen, found);
        }
        for (Report report : memo.answer().reports()) {
            found.add(new Found(key.module(), key.sourceId(), report));
        }
    }

    private void recordRead(Key<?> key) {
        Set<Key<?>> frame = frames.peek();
        if (frame != null) {
            frame.add(key);
        }
    }
}
