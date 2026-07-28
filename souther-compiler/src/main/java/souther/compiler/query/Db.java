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
 * <p>That rests on the answers being values, and two of them carry it. {@link Front.Layout} is what
 * stops an edit to any source from reaching the whole workspace: every parse feeds it, and it comes
 * out the same. {@link Names.Declarations} is what stops an edit at the module boundary: an importer
 * builds against what a module declares, not against its bodies. Both are maps of records, and
 * {@code IncrementalCompilationTest} pins both.
 *
 * <p>It does not hold everywhere. A module's classes are a {@code Map<String, byte[]>}, and arrays
 * compare by identity, so regenerating them always counts as a change — and every module's examples
 * read every module's classes. Comparing the bytes would not help: after a real edit they differ.
 * What would is for an example to depend on the classes it reaches rather than on all of them,
 * which is per-definition work and not here.
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
     * asked first; the whole chain in flight is discarded, not only the part inside the cycle,
     * because an answer built from a cyclic one is as entry-dependent as the cyclic one.
     *
     * <p>That is more than the cycle, and it costs: while one exists, every key that reached it is
     * recomputed on every ask. It is affordable because nothing in a compile is supposed to get
     * here — modules that name each other are found by {@link Names.Cycles} and stopped before any
     * question is asked that would answer itself.
     */
    private final Set<Key<?>> throughCycle = new HashSet<>();
    /** Every key that has ever reported something, in the order it first did — the order reports
     * are read back in. */
    private final List<Key<?>> spoke = new ArrayList<>();
    private final Set<Key<?>> hasSpoken = new LinkedHashSet<>();

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

    /**
     * Drops everything kept about a source that is no longer part of this compilation — its text,
     * and every answer that was about it or about the module it declared.
     *
     * <p>A store lives as long as the workspace does, so what it keeps about a file it will never be
     * asked about again is held for nothing. Dropping an answer is always safe: the next question
     * that wants it computes it.
     */
    public void forget(String sourceId, String moduleName) {
        set(new Front.Text(sourceId), null);
        // Dropping by module name is exact, not approximate. Every question about a module reads its
        // declaring source through the workspace layout, and the layout names one source per module
        // however many claim it — so while this source was the module, every answer about that module
        // was an answer about this source. A source that claimed a name it did not get is passed a
        // null module name and takes nothing else with it.
        memos.keySet().removeIf(key -> sourceId.equals(key.sourceId())
                || (moduleName != null && moduleName.equals(key.module())));
        hasSpoken.removeIf(key -> !memos.containsKey(key));
        spoke.removeIf(key -> !memos.containsKey(key));
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
        // This key leaves nothing of itself behind, whether it answered or threw: not its frame, not
        // its place in the chain, not a cycle mark. A compile error is a value, so a throw is an
        // internal fault, and a store kept across edits would otherwise never keep this key again.
        //
        // What a dependency answered before the throw is kept, and should be: a query is a function
        // of its inputs, so an answer that was reached is as good as any other. Only the key that
        // failed is unfinished.
        boolean reachedThroughCycle = false;
        try {
            answer = key.compute(this);
        } finally {
            // In the order they were read, so a caller walking the graph for reports meets them in
            // the order the work happened. An unordered copy here makes the first error a module
            // reports depend on hash order.
            read = Collections.unmodifiableSet(frames.pop());
            inProgress.remove(key);
            reachedThroughCycle = throughCycle.remove(key);
        }
        if (!reachedThroughCycle) {
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
     * Everything this compilation now has to report, in the order the keys first reported it.
     *
     * <p>Only questions asked since the last input changed are read. A question that was asked and
     * recomputed contributes what it says now, so a problem that was fixed is not still listed —
     * and a question that stopped being asked contributes nothing, because there is no longer
     * anything that wants to know. Deleting the last row of an {@code examples for} file is the
     * second case: nothing asks whether that file's rows hold any more, so nothing recomputes the
     * answer, and reading it would put a failure on a line that is not there.
     *
     * <p>Being asked is what {@code verifiedAt} records. Answering a key sets it, and so does finding
     * that a kept answer still holds, so every key reached since the last input change carries this
     * revision and every key that was not reached carries an older one.
     *
     * <p>"Since the last input change" is not "in the last round of asking", and the two come apart
     * if a caller asks for less than it did before without changing anything: what the wider round
     * reached still counts as reached. Every caller here asks for the whole compilation, so it does
     * not arise — but a caller that asked only about the file in front of the author would need a
     * generation of its own, separate from the input revision.
     */
    public List<Found> allReports() {
        Map<String, Found> found = new java.util.LinkedHashMap<>();
        for (Key<?> key : spoke) {
            Memo memo = memos.get(key);
            if (memo == null || memo.verifiedAt() != revision) {
                continue;
            }
            for (Report report : memo.answer().reports()) {
                // One problem is one diagnostic, whichever questions found it. Two of them can, and
                // legitimately: a helper is checked on its own and again in each body it is expanded
                // into, and both are looking at the same line. The first to say it is the one that
                // says it, so the order is the order the work happened in.
                found.putIfAbsent(
                        key.module() + " " + key.sourceId() + " " + report.problem(),
                        new Found(key.module(), key.sourceId(), report));
            }
        }
        return new ArrayList<>(found.values());
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

    private void recordRead(Key<?> key) {
        Set<Key<?>> frame = frames.peek();
        if (frame != null) {
            frame.add(key);
        }
    }
}
