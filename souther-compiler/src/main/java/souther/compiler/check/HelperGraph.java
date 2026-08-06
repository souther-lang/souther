package souther.compiler.check;

import souther.compiler.ast.Ast;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

/**
 * Which declaration calls which, over one {@link HelperTable}, and which of them recurse.
 *
 * <p>A function of the table it was built from and of nothing else. Two bodies of one module are
 * expanded against one table and so read one graph — before this each expansion built its own, which
 * meant walking every one of the standard library's bodies again for each, and eleven answers that
 * had to agree.
 *
 * <p>A helper recurses iff it can reach itself through helper calls; every member of a mutual cycle
 * is reached from itself, so all are marked. Both a module's own helpers and the shipped prelude ones
 * are walked: {@code List.foldFrom} is a recursive prelude helper and has to be left standing —
 * lowered to a method, not inlined — exactly as a module-own recursive helper is, or its self-call is
 * expanded forever.
 *
 * <p>Built over the table as it stands. A table narrowed for an expansion ({@link HelperTable#hiding})
 * narrows what a call reaches and changes nothing here: a graph taken over the narrowed table would
 * find the very helper being expanded non-recursive.
 */
public record HelperGraph(Map<String, Set<String>> callsOf, Set<String> recursive) {

    /** The graph of {@code table}: what each declaration in it calls, and which of them recurse. */
    public static HelperGraph of(HelperTable table) {
        Map<String, Set<String>> callsOf = new LinkedHashMap<>();
        for (Map.Entry<String, Ast.FnDef> e : table.reachable().entrySet()) {
            Set<String> called = new LinkedHashSet<>();
            HelperInliner.helperCallsIn(e.getValue().writtenBody(), table.reachable(), called);
            callsOf.put(e.getKey(), called);
        }
        Set<String> recursive = new LinkedHashSet<>();
        for (String name : table.reachable().keySet()) {
            if (reaches(callsOf, name, name, new HashSet<>())) {
                recursive.add(name);
            }
        }
        return new HelperGraph(fixed(callsOf), Set.copyOf(recursive));
    }

    /**
     * {@code callsOf} as a graph nothing can change, edges included.
     *
     * <p>Fixing the map alone leaves each of its sets the one that was built here, and both accessors
     * hand one out. A graph is a module's answer and it is shared: what one reader did to it would be
     * what every reader after it read, and a query answer that changes under its readers is one the
     * store cannot tell has changed.
     */
    private static Map<String, Set<String>> fixed(Map<String, Set<String>> callsOf) {
        Map<String, Set<String>> out = new LinkedHashMap<>();
        callsOf.forEach((name, called) -> out.put(name, Collections.unmodifiableSet(called)));
        return Collections.unmodifiableMap(out);
    }

    /** Whether {@code name} is on a call cycle, so a call of it is left standing rather than
     * expanded (spec 13.1). */
    public boolean recurses(String name) {
        return recursive.contains(name);
    }

    /** What {@code name}'s body calls directly, or an empty set where it calls nothing this table
     * reaches. */
    public Set<String> calls(String name) {
        return callsOf.getOrDefault(name, Set.of());
    }

    /** Everything reachable from {@code seeds} through call edges, the seeds included. */
    public Set<String> reachedFrom(Collection<String> seeds) {
        Set<String> reached = new LinkedHashSet<>(seeds);
        Deque<String> work = new ArrayDeque<>(seeds);
        while (!work.isEmpty()) {
            for (String called : calls(work.poll())) {
                if (reached.add(called)) {
                    work.add(called);
                }
            }
        }
        return reached;
    }

    /** Whether {@code target} is reachable from {@code from}. Prelude helpers never call a module's
     * own helpers, so a cycle stays within the module's own helpers. */
    private static boolean reaches(Map<String, Set<String>> callsOf, String from, String target,
                                   Set<String> seen) {
        Set<String> called = callsOf.get(from);
        if (called == null) {
            return false;
        }
        for (String c : called) {
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
