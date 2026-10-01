package souther.compiler.check;

import souther.compiler.types.ReachName;

import java.util.AbstractList;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.RandomAccess;
import java.util.Set;

/**
 * Which declaration calls which, over one {@link HelperTable}, and which of them recurse.
 *
 * <p>Over references and not over addresses or spellings. An edge here says that what a module
 * reaches one way calls what it reaches another, which is a fact about resolved references; where
 * the module puts the methods it emits for them is a different question and is nowhere in this.
 *
 * <p>Calls and nothing else. A body also reaches the values it reads, and runs them; which is which is
 * {@link HelperEdges}'s to say, and a read is not an edge here, because recursion is a cycle of calls.
 *
 * <p>A function of the table it was built from and of nothing else. Two bodies of one module are
 * expanded against one table and so read one graph — before this each expansion built its own, which
 * meant walking every one of the standard library's bodies again for each, and eleven answers that
 * had to agree.
 *
 * <p>A helper recurses iff it can reach itself through helper calls; every member of a mutual cycle
 * is reached from itself, so all are marked. {@code recursive} is a {@link List} — not a set of any
 * kind — because the order is part of what it answers: a reader that reports one member of a cycle
 * reports the one it reaches first, and the order it reaches them in is the order they were declared.
 * Said in the type rather than in a comment, because a {@code Set}'s {@code equals} answers about
 * membership only — the very question issue #1835 asked of {@code RequiredRecursiveDefs}, whose
 * changedAt this graph feeds. A set that only promises membership may also be copied into one whose
 * iteration order the JVM salts per run — which is how the same source came to name a different
 * helper on a different run. Both a module's own helpers and the shipped prelude ones
 * are walked: {@code List.foldFrom} is a recursive prelude helper and has to be left standing —
 * lowered to a method, not inlined — exactly as a module-own recursive helper is, or its self-call is
 * expanded forever.
 *
 * <p>Built over the table as it stands. A table narrowed for an expansion ({@link HelperTable#hiding})
 * narrows what a call reaches and changes nothing here: a graph taken over the narrowed table would
 * find the very helper being expanded non-recursive.
 *
 * <p>{@link #recurses} is asked for each call while bodies are expanded and lowered, and a module has
 * as many recursions as it was written with, together with every one in the prelude and its imports.
 * So {@code recursive} is a list that answers membership by hash: the order is still the list's and
 * is all its {@code equals} compares, and the index is part of how the list is held, not a second
 * component that would have to agree with it. Every graph holds one, however it was built, because
 * the constructor makes it.
 */
public record HelperGraph(Map<ReachName.Declaration, Set<ReachName.Declaration>> callsOf,
                          List<ReachName.Declaration> recursive) {

    public HelperGraph {
        recursive = Recursions.of(recursive);
    }

    /** The graph of {@code table}: what each declaration in it calls, and which of them recurse. */
    public static HelperGraph of(HelperTable table) {
        Map<ReachName.Declaration, Set<ReachName.Declaration>> callsOf = new LinkedHashMap<>();
        for (Map.Entry<ReachName.Declaration, HelperEntry> e : table.reachable().entrySet()) {
            callsOf.put(e.getKey(), HelperEdges.in(table.library(),
                    e.getValue().definition().writtenBody(), table.reachable()).calls());
        }
        Map<ReachName.Declaration, Set<ReachName.Declaration>> onACycle = Cycles.groups(callsOf);
        List<ReachName.Declaration> recursive = new ArrayList<>();
        for (ReachName.Declaration reference : table.reachable().keySet()) {
            if (onACycle.containsKey(reference)) {
                recursive.add(reference);
            }
        }
        return new HelperGraph(fixed(callsOf), recursive);
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

    /**
     * Each declaration on a call cycle, mapped to the declarations on it: those it reaches through
     * calls that reach it back, itself among them. A declaration that does not recurse is not a key.
     *
     * <p>The groups are the ones {@link #of} decides {@code recursive} with. So a declaration
     * {@link #recurses} holds has a cycle here, and one it does not hold has none, by the one
     * computation and not by two that happen to agree. A reader that relies on this — a group proven
     * total is a group of no graphs where it is empty — still holds it to that
     * ({@link TotalityChecker}).
     *
     * <p>Each cycle in the order the table holds its members, which is the order they were declared,
     * and one list shared by every member of it. All of them at once, because a reader asking for
     * one declaration's cycle asks for the next one's after it, and each answer is a walk of the
     * whole graph. Worked out of the edges when asked rather than kept beside them: a graph's
     * {@code equals} is what an answer built on it is compared by, and a second statement of the same
     * edges would be a component that could only agree with them or be wrong.
     */
    public Map<ReachName.Declaration, List<ReachName.Declaration>> callCycles() {
        Map<ReachName.Declaration, Set<ReachName.Declaration>> groups = Cycles.groups(callsOf);
        // By identity: every member of a group maps to the one set, and a set's own equals would
        // read the whole group for each member.
        Map<Set<ReachName.Declaration>, List<ReachName.Declaration>> declared = new IdentityHashMap<>();
        for (ReachName.Declaration member : callsOf.keySet()) {
            Set<ReachName.Declaration> group = groups.get(member);
            if (group != null) {
                declared.computeIfAbsent(group, _ -> new ArrayList<>()).add(member);
            }
        }
        declared.replaceAll((_, members) -> List.copyOf(members));
        Map<ReachName.Declaration, List<ReachName.Declaration>> cycles = new LinkedHashMap<>();
        for (ReachName.Declaration member : callsOf.keySet()) {
            Set<ReachName.Declaration> group = groups.get(member);
            if (group != null) {
                cycles.put(member, declared.get(group));
            }
        }
        return Collections.unmodifiableMap(cycles);
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

    /**
     * The recursions in order, with their membership answered by hash.
     *
     * <p>A {@link List} in everything a reader can tell: it iterates, compares and hashes as the
     * sequence it holds, so it equals any list of the same declarations in the same order and no
     * other. Only {@link #contains} reads the set, which holds the same declarations and so cannot
     * answer differently from a scan of them.
     */
    private static final class Recursions extends AbstractList<ReachName.Declaration>
            implements RandomAccess {

        private final List<ReachName.Declaration> ordered;
        private final Set<ReachName.Declaration> members;

        private Recursions(List<ReachName.Declaration> ordered) {
            this.ordered = ordered;
            this.members = Set.copyOf(ordered);
        }

        static List<ReachName.Declaration> of(List<ReachName.Declaration> recursive) {
            if (recursive instanceof Recursions already) {
                return already;
            }
            List<ReachName.Declaration> ordered = List.copyOf(recursive);
            return ordered.isEmpty() ? ordered : new Recursions(ordered);
        }

        @Override
        public ReachName.Declaration get(int index) {
            return ordered.get(index);
        }

        @Override
        public int size() {
            return ordered.size();
        }

        @Override
        public boolean contains(Object o) {
            return members.contains(o);
        }
    }
}
