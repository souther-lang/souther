package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.types.ValueName;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.TreeSet;

/**
 * Which declarations reach a {@code partial} helper, and by which path.
 *
 * <p>A helper written without {@code partial} carries Souther's termination guarantee, and it carries
 * it for everything it calls as well (spec §fn-rules). What decides that is reachability over the call
 * graph, so the question is asked here once and answered for both of the places that ask it: the
 * totality check, which requires that no unmarked helper reaches a marked one, and the invariant
 * check, which requires that no clause does.
 *
 * <p>This graph is not the one {@code TotalityChecker} builds for size-change analysis. That one has
 * the module's own helpers as its nodes, because a strongly-connected group is a group of definitions
 * this module can see the bodies of. This one reaches past the module: a call to an imported helper is
 * an edge, and the imported helper is a terminal answered by the word written on its declaration. That
 * is sound because the exporting module was compiled under the same rule, which is what
 * {@link souther.compiler.codegen.Backend#BOUNDARY_VERSION} records — an unmarked published helper
 * summarises its whole call closure, so a reader never walks it.
 *
 * <p>A path is the shortest one, found breadth-first with each node's callees taken in name order, so
 * the same module always reports the same path.
 */
final class PartialReachability {

    /** Module-own helper -> the helpers it calls, in name order. A name absent as a key is a terminal:
     * an imported or prelude helper, whose declaration answers for its own closure. */
    private final Map<String, List<String>> calls;

    /** Every helper reached from this module that is written {@code partial}, own or imported. */
    private final Set<String> partial;

    private final HelperInliner inliner;

    private PartialReachability(Map<String, List<String>> calls, Set<String> partial,
                                HelperInliner inliner) {
        this.calls = calls;
        this.partial = partial;
        this.inliner = inliner;
    }

    static PartialReachability of(HelperInliner inliner) {
        Map<String, List<String>> calls = new LinkedHashMap<>();
        Set<String> partial = new HashSet<>();
        for (Map.Entry<String, Ast.FnDef> entry : inliner.helpers().entrySet()) {
            Ast.FnDef helper = entry.getValue();
            if (!(helper.body() instanceof Ast.FnBody.Written written)) {
                continue;   // an intrinsic declares no body to read calls out of
            }
            calls.put(entry.getKey(), callsOf(written.expr(), inliner));
            if (helper.partial()) {
                partial.add(entry.getKey());
            }
        }
        for (List<String> callees : List.copyOf(calls.values())) {
            for (String callee : callees) {
                if (calls.containsKey(callee)) {
                    continue;
                }
                Ast.FnDef declared = inliner.helper(callee);
                if (declared != null && declared.partial()) {
                    partial.add(callee);
                }
            }
        }
        return new PartialReachability(calls, partial, inliner);
    }

    /**
     * Whether {@code v} names a {@code partial} helper that takes arguments — the one thing that may
     * not be written where a value goes. A value takes none and is read rather than handed over.
     *
     * <p>Both spellings are tried, because a name is written bare where an import let it be and the
     * table is keyed by the qualified name the declaration is reached by. Asking with only what was
     * written misses an imported helper silently, which is what a table keyed by names does with a key
     * it has not got.
     */
    boolean isPartialFunctionNamed(Ast.Var v) {
        if (!(v.denotes() instanceof ValueName.Helper helper)) {
            return false;
        }
        Ast.FnDef declared = inliner.helper(v.reaches());
        if (declared == null) {
            declared = inliner.helper(helper.module() + "." + helper.name());
        }
        return declared != null && declared.partial() && !declared.params().isEmpty();
    }

    /**
     * The shortest path from {@code helper} to a {@code partial} one, {@code helper} first and the
     * {@code partial} one last, or empty where it reaches none. {@code helper}'s own marker is not
     * read — this answers what it reaches, not what it is.
     */
    Optional<List<String>> fromHelper(String helper) {
        return search(calls.getOrDefault(helper, List.of())).map(path -> prepend(helper, path));
    }

    /**
     * The shortest path from the helpers {@code e} calls to a {@code partial} one, or empty where it
     * reaches none. The expression is not on the path — its caller names what it is.
     */
    Optional<List<String>> fromExpression(Ast.Expr e) {
        return search(callsOf(e, inliner));
    }

    /** A path as a report writes it: {@code depth -> measure -> spin}. */
    static String render(List<String> path) {
        return String.join(" -> ", path);
    }

    /**
     * Breadth-first from {@code seeds}, stopping at the first {@code partial} node reached. A
     * {@code partial} node is not expanded: what it reaches is its own business and says nothing more
     * about the caller. A node is visited once, so a cycle is walked once.
     */
    private Optional<List<String>> search(List<String> seeds) {
        Map<String, String> from = new HashMap<>();
        Set<String> seen = new HashSet<>();
        Deque<String> work = new ArrayDeque<>();
        for (String seed : seeds) {
            if (!seen.add(seed)) {
                continue;
            }
            if (partial.contains(seed)) {
                return Optional.of(List.of(seed));
            }
            work.add(seed);
        }
        while (!work.isEmpty()) {
            String at = work.poll();
            for (String next : calls.getOrDefault(at, List.of())) {
                if (!seen.add(next)) {
                    continue;
                }
                from.put(next, at);
                if (partial.contains(next)) {
                    return Optional.of(pathTo(next, from));
                }
                work.add(next);
            }
        }
        return Optional.empty();
    }

    private static List<String> pathTo(String end, Map<String, String> from) {
        List<String> path = new ArrayList<>();
        for (String at = end; at != null; at = from.get(at)) {
            path.add(at);
        }
        Collections.reverse(path);
        return List.copyOf(path);
    }

    private static List<String> prepend(String head, List<String> tail) {
        List<String> path = new ArrayList<>();
        path.add(head);
        path.addAll(tail);
        return List.copyOf(path);
    }

    /**
     * The helpers {@code e} runs, in name order: the ones it applies, and the values it reads.
     *
     * <p>A {@code let} written with no parameter list is a value, and reading its name runs its body —
     * it is substituted at the reference (ADR-0072), so what it reaches is reached from here. A name
     * that stands for a helper <em>taking</em> arguments is a different thing: written where a value
     * goes it becomes a function, and a {@code partial} one may not be written there at all
     * (spec §fn-rules), which is checked on its own and is why no edge is made for it here.
     */
    private static List<String> callsOf(Ast.Expr e, HelperInliner inliner) {
        Set<String> called = new TreeSet<>();
        collectCalls(e, inliner, called);
        return List.copyOf(called);
    }

    private static void collectCalls(Ast.Expr e, HelperInliner inliner, Set<String> out) {
        switch (e) {
            case Ast.Apply call when inliner.helper(call.reaches()) != null -> out.add(call.reaches());
            case Ast.Var v when v.denotes() instanceof ValueName.Helper -> {
                Ast.FnDef read = inliner.helper(v.reaches());
                if (read != null && read.params().isEmpty()) {
                    out.add(v.reaches());
                }
            }
            default -> { }
        }
        Ast.forEachChild(e, child -> collectCalls(child, inliner, out));
    }
}
