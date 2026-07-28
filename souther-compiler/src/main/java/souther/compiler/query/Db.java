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
 * keeping the answer, and handing the same answer to everyone who asks again.
 *
 * <p>It also watches. While a key is being answered, every key it asks is recorded against it, so
 * afterwards the graph knows what each answer was built from. That record is what an editor's
 * recompile will read to find the answers an edit can have changed, and it is what makes a question
 * that depends on itself visible at the moment it happens rather than as a stack overflow.
 *
 * <p>One store is one compilation. It is not thread-safe and does not need to be: the work inside a
 * compile is a graph walk, not a set of independent jobs.
 */
public final class Db {

    private final Map<Key<?>, Answer<?>> answers = new HashMap<>();
    /** What each answered key read while it was being answered. */
    private final Map<Key<?>, Set<Key<?>>> reads = new HashMap<>();
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
    /** Every key that reported something, and what it reported, in the order the answers finished. */
    private final Map<Key<?>, Answer<?>> told = new HashMap<>();
    private final List<Key<?>> order = new ArrayList<>();

    /** Gives an input its value. Returns this store, so a compilation can be set up in one
     * expression. */
    public <T> Db set(Input<T> key, T value) {
        answers.put(key, Answer.of(value));
        return this;
    }

    /** Answers {@code key}, computing it if this is the first time it has been asked. */
    @SuppressWarnings("unchecked")
    public <T> Answer<T> ask(Key<T> key) {
        recordRead(key);
        Answer<?> known = answers.get(key);
        if (known != null) {
            return (Answer<T>) known;
        }
        if (inProgress.contains(key)) {
            // Everything in flight has now seen an answer that depends on where it was entered.
            throughCycle.addAll(inProgress);
            return key.onCycle(List.copyOf(inProgress));
        }
        inProgress.add(key);
        frames.push(new LinkedHashSet<>());
        Answer<T> answer;
        try {
            answer = key.compute(this);
        } finally {
            // In the order they were read, so a caller walking the graph for reports meets them in
            // the order the passes ran. An unordered copy here makes the first error a module
            // reports depend on hash order.
            reads.put(key, Collections.unmodifiableSet(frames.pop()));
            inProgress.remove(key);
        }
        if (!throughCycle.remove(key)) {
            answers.put(key, answer);
        }
        if (!answer.reports().isEmpty() && told.putIfAbsent(key, answer) == null) {
            order.add(key);
        }
        return answer;
    }

    /**
     * Everything reported by every question this store has answered, in the order the answers were
     * finished — which is the order the work happened, innermost first. A caller that stops at the
     * first error stops at the same one a pipeline would have raised.
     */
    public List<Found> allReports() {
        List<Found> found = new ArrayList<>();
        for (Key<?> key : order) {
            for (Report report : told.get(key).reports()) {
                found.add(new Found(key.module(), key.sourceId(), report));
            }
        }
        return found;
    }

    /** What {@code key} read while it was answered, empty if it has not been asked. */
    public Set<Key<?>> dependenciesOf(Key<?> key) {
        return reads.getOrDefault(key, Set.of());
    }

    /** Whether {@code key}'s answer is being kept — it has been asked, and was not reached through
     * a cycle. */
    public boolean isComputed(Key<?> key) {
        return answers.containsKey(key);
    }

    /** A report and the module whose source it belongs to, which may be null. */
    public record Found(String module, String sourceId, Report report) {}

    /**
     * Everything reported while answering {@code root}, and by everything answering it needed.
     * Deepest first — a module's own errors come before those of a module that read it — so a
     * caller that stops at the first error stops at the same one the passes used to raise.
     *
     * <p>Each report is attributed to the module its key was about, so an error in an imported
     * module lands on that module's source however far away it was asked for.
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
        for (Key<?> read : reads.getOrDefault(key, Set.of())) {
            gather(read, seen, found);
        }
        Answer<?> answer = answers.get(key);
        if (answer == null) {
            return;
        }
        for (Report report : answer.reports()) {
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
