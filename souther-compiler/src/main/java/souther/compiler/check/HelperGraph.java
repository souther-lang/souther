package souther.compiler.check;

import souther.compiler.types.ReachName;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.SequencedSet;
import java.util.Set;

/**
 * Which declaration calls which, over one {@link HelperTable}, and which of them recurse.
 *
 * <p>Over references and not over addresses or spellings. An edge here says that what a module
 * reaches one way calls what it reaches another, which is a fact about resolved references; where
 * the module puts the methods it emits for them is a different question and is nowhere in this.
 *
 * <p>A function of the table it was built from and of nothing else. Two bodies of one module are
 * expanded against one table and so read one graph — before this each expansion built its own, which
 * meant walking every one of the standard library's bodies again for each, and eleven answers that
 * had to agree.
 *
 * <p>A helper recurses iff it can reach itself through helper calls; every member of a mutual cycle
 * is reached from itself, so all are marked. {@code recursive} is a {@link SequencedSet} because the
 * order is part of what it answers: a reader that reports one member of a cycle reports the one it
 * reaches first, and the order it reaches them in is the order they were declared. Said in the type
 * rather than in a comment, because a set that only promises membership may be copied into one whose
 * iteration order the JVM salts per run — which is how the same source came to name a different
 * helper on a different run. Both a module's own helpers and the shipped prelude ones
 * are walked: {@code List.foldFrom} is a recursive prelude helper and has to be left standing —
 * lowered to a method, not inlined — exactly as a module-own recursive helper is, or its self-call is
 * expanded forever.
 *
 * <p>Built over the table as it stands. A table narrowed for an expansion ({@link HelperTable#hiding})
 * narrows what a call reaches and changes nothing here: a graph taken over the narrowed table would
 * find the very helper being expanded non-recursive.
 */
public record HelperGraph(Map<ReachName.Declaration, Set<ReachName.Declaration>> callsOf,
                          SequencedSet<ReachName.Declaration> recursive) {

    /** The graph of {@code table}: what each declaration in it calls, and which of them recurse. */
    public static HelperGraph of(HelperTable table) {
        Map<ReachName.Declaration, Set<ReachName.Declaration>> callsOf = new LinkedHashMap<>();
        for (Map.Entry<ReachName.Declaration, HelperEntry> e : table.reachable().entrySet()) {
            Set<ReachName.Declaration> called = new LinkedHashSet<>();
            HelperInliner.helperCallsIn(table.library(), e.getValue().definition().writtenBody(),
                    table.reachable(), called);
            callsOf.put(e.getKey(), called);
        }
        SequencedSet<ReachName.Declaration> recursive = new LinkedHashSet<>();
        for (ReachName.Declaration reference : table.reachable().keySet()) {
            if (reaches(callsOf, reference, reference, new HashSet<>())) {
                recursive.add(reference);
            }
        }
        return new HelperGraph(fixed(callsOf), Collections.unmodifiableSequencedSet(recursive));
    }

    /**
     * {@code callsOf} as a graph nothing can change, edges included.
     *
     * <p>Fixing the map alone leaves each of its sets the one that was built here, and both accessors
     * hand one out. A graph is a module's answer and it is shared: what one reader did to it would be
     * what every reader after it read, and a query answer that changes under its readers is one the
     * store cannot tell has changed.
     */
    private static Map<ReachName.Declaration, Set<ReachName.Declaration>> fixed(
            Map<ReachName.Declaration, Set<ReachName.Declaration>> callsOf) {
        Map<ReachName.Declaration, Set<ReachName.Declaration>> out = new LinkedHashMap<>();
        callsOf.forEach((name, called) -> out.put(name, Collections.unmodifiableSet(called)));
        return Collections.unmodifiableMap(out);
    }

    /** Whether {@code reference} is on a call cycle, so a call of it is left standing rather than
     * expanded (spec §fn-declaration). */
    public boolean recurses(ReachName.Declaration reference) {
        return recursive.contains(reference);
    }

    /** What {@code reference}'s body calls directly, or an empty set where it calls nothing this
     * table reaches. */
    public Set<ReachName.Declaration> calls(ReachName.Declaration reference) {
        return callsOf.getOrDefault(reference, Set.of());
    }

    /** Everything reachable from {@code seeds} through call edges, the seeds included. */
    public Set<ReachName.Declaration> reachedFrom(Collection<ReachName.Declaration> seeds) {
        Set<ReachName.Declaration> reached = new LinkedHashSet<>(seeds);
        Deque<ReachName.Declaration> work = new ArrayDeque<>(seeds);
        while (!work.isEmpty()) {
            for (ReachName.Declaration called : calls(work.poll())) {
                if (reached.add(called)) {
                    work.add(called);
                }
            }
        }
        return reached;
    }

    /** Whether {@code target} is reachable from {@code from}. The library's helpers never call a module's
     * own helpers, so a cycle stays within the module's own helpers. */
    private static boolean reaches(Map<ReachName.Declaration, Set<ReachName.Declaration>> callsOf,
                                   ReachName.Declaration from, ReachName.Declaration target,
                                   Set<ReachName.Declaration> seen) {
        Set<ReachName.Declaration> called = callsOf.get(from);
        if (called == null) {
            return false;
        }
        for (ReachName.Declaration c : called) {
            if (c.equals(target)) {
                return true;
            }
            if (seen.add(c) && reaches(callsOf, c, target, seen)) {
                return true;
            }
        }
        return false;
    }
}
