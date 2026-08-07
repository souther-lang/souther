package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.types.ReachName;
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
 * <p>Which of the two a helper is comes from its declaration. A module emits the recursive helpers it
 * reaches as its own methods, so an imported one sits in this module's fns under a name of the same
 * shape as the module's own; the declaration is the only thing that still says who wrote it
 * ({@link Ast.FnDef#declaredBy}). Deciding it any other way is deciding it by spelling, and this is a
 * rule about which module carries the guarantee.
 *
 * <p>Three things are asked of a declaration rather than of this graph, because a soundness rule may
 * not rest on what building the graph happened to visit. Whether a name is {@code partial} is read off
 * the declaration it reaches, not off a set collected on the way — a clause names what it names,
 * whether or not a helper of this module names it too. And which declaration a name reaches is read
 * off the name the reference carries, not off how it was spelled, so the answer is
 * the same before and after the pass that writes an imported name out qualified.
 *
 * <p>A path is the shortest one, found breadth-first with each node's callees taken in name order, so
 * the same module always reports the same path.
 */
final class PartialReachability {

    /** A helper this module declared -> the helpers it reaches, in name order. A name absent as a
     * key is a terminal: an imported or prelude helper, whose declaration answers for its own
     * closure. Which of the two a name is comes from the declaration and not from the name, since a
     * module's fns hold both under names of one shape. */
    private final Map<String, List<String>> calls;

    private final HelperInliner inliner;

    private PartialReachability(Map<String, List<String>> calls, HelperInliner inliner) {
        this.calls = calls;
        this.inliner = inliner;
    }

    static PartialReachability of(HelperInliner inliner) {
        Map<String, List<String>> calls = new LinkedHashMap<>();
        for (Map.Entry<String, Ast.FnDef> entry : inliner.held().entrySet()) {
            // Only what this module declared is a node. What it took on to emit — a prelude helper,
            // one another module published — is a terminal, because its declaration already answers
            // for its whole closure (ADR-0098). It is in the same map and under a name of the same
            // shape, so the declaration is what tells the two apart.
            if (!entry.getValue().declaredBy(inliner.moduleName())) {
                continue;
            }
            if (entry.getValue().body() instanceof Ast.FnBody.Written written) {
                calls.put(entry.getKey(), reachedBy(written.expr(), inliner));
            }
            // an intrinsic declares no body to read what it reaches out of
        }
        return new PartialReachability(calls, inliner);
    }

    /**
     * Whether the declaration filed under {@code name} is {@code partial}.
     *
     * <p>Asked of the declaration, never of a set of names collected while building the graph. A set
     * answers correctly only for what the collection happened to visit, and this question is put to
     * names the collection never sees — an invariant clause names what it names, whether or not a
     * helper of this module names it too. Which of them are visited is another pass's business, so a
     * soundness rule may not rest on it.
     */
    private boolean isPartial(String name) {
        Ast.FnDef declared = inliner.helper(name);
        return declared != null && declared.partial();
    }

    /**
     * Whether {@code v} names a {@code partial} helper that takes arguments — the one thing that may
     * not be written where a value goes. A value takes none and is read rather than handed over.
     */
    boolean isPartialFunctionNamed(Ast.Var v) {
        Ast.FnDef declared = declarationOf(v.denotes(), v.reachedAs(), inliner);
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
        return search(reachedBy(e, inliner));
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
            if (isPartial(seed)) {
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
                if (isPartial(next)) {
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
    private static List<String> reachedBy(Ast.Expr e, HelperInliner inliner) {
        Set<String> reached = new TreeSet<>();
        collectReached(e, inliner, reached);
        return List.copyOf(reached);
    }

    private static void collectReached(Ast.Expr e, HelperInliner inliner, Set<String> out) {
        switch (e) {
            case Ast.Apply call -> {
                Ast.FnDef applied = declarationOf(call.denotes(), call.reachedAs(), inliner);
                if (applied != null) {
                    out.add(keyOf(call.denotes(), call.reachedAs()));
                }
            }
            case Ast.Var v -> {
                Ast.FnDef read = declarationOf(v.denotes(), v.reachedAs(), inliner);
                if (read != null && read.params().isEmpty()) {
                    out.add(keyOf(v.denotes(), v.reachedAs()));
                }
            }
            default -> { }
        }
        Ast.forEachChild(e, child -> collectReached(child, inliner, out));
    }

    /**
     * The key {@code denotes} is filed under, or null where it denotes nothing a helper table holds.
     *
     * <p>The one place a name becomes a node. Every question here goes through it — the graph's edges,
     * the marker lookup and the value-position check — so none of them can disagree about which
     * declaration a name reached, and none of them depends on how it was spelled.
     *
     * <p>A library name is a node like any other. The standard library declares nothing {@code partial}
     * today, so keeping it changes no answer; leaving it out would make that a premise of the check
     * rather than a fact about the library, and one the library could stop honouring in silence.
     */
    private static String keyOf(ValueName denotes, ReachName reachedAs) {
        return switch (denotes) {
            // Which key it is, the reference says: settled where the name was resolved and carried
            // here. What decides whether there is a node at all is what the name denotes — a binding
            // spelled like a helper reaches no declaration however it is written.
            case ValueName.Helper _, ValueName.Stdlib _ -> reachedAs.rendered();
            case null, default -> null;
        };
    }

    private static Ast.FnDef declarationOf(ValueName denotes, ReachName reachedAs,
                                           HelperInliner inliner) {
        String key = keyOf(denotes, reachedAs);
        return key == null ? null : inliner.helper(key);
    }
}
