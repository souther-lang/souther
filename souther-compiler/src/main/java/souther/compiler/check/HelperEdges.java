package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.ReachName;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

/**
 * What one body reaches directly, by the two ways a body reaches a declaration.
 *
 * <p>A call applies a declaration. A sugar is counted as the call it is written out as, since that is
 * the declaration the body ends up running. A read names a declaration written with no parameter list
 * where a value goes: the value's body runs where it is read (spec §fn-rules), so what it reaches is
 * reached from here, but reading it is not calling it. Recursion is a cycle of calls
 * (spec §fn-declaration), and a read on the way does not close one; what a body runs, which is what
 * the termination guarantee is about, is both. A name that stands for a helper taking arguments,
 * written where a value goes, is neither: it becomes a function there, and is checked on its own.
 *
 * <p>{@code calls} also holds the target of a {@link Hir.ValueInvocation}. A body as written has
 * none; lowering writes one where a value's method is called, and that call is an edge of the graph
 * over whatever body holds it.
 *
 * <p>Asked against the declarations {@code reachable} holds and nothing else, so a name that reaches
 * nothing there is no edge. Which declarations those are is the caller's to say: a table narrowed for
 * an expansion reaches less than the one the call graph is built over.
 *
 * <p>Edges out of one body, and nothing about a graph. Which bodies are nodes, which are followed past
 * and in what order, is each reader's own.
 */
record HelperEdges(Set<ReachName.Declaration> calls, Set<ReachName.Declaration> valueReads) {

    /** The edges out of {@code body}, each in the order it is first met. */
    static HelperEdges in(Stdlib stdlib, Hir.Expr body,
                          Map<ReachName.Declaration, HelperEntry> reachable) {
        Set<ReachName.Declaration> calls = new LinkedHashSet<>();
        Set<ReachName.Declaration> reads = new LinkedHashSet<>();
        collect(stdlib, body, reachable, calls, reads);
        return new HelperEdges(Collections.unmodifiableSet(calls), Collections.unmodifiableSet(reads));
    }

    private static void collect(Stdlib stdlib, Hir.Expr e,
                                Map<ReachName.Declaration, HelperEntry> reachable,
                                Set<ReachName.Declaration> calls, Set<ReachName.Declaration> reads) {
        switch (e) {
            // Applying a function-typed parameter, or a binding holding a function, is not a call to
            // whatever else bears that name: the call carries what it resolved to, and is asked.
            case Hir.Apply call -> {
                ReachName.Declaration applied = HelperInliner.calledHelper(stdlib, call);
                if (applied != null && reachable.containsKey(applied)) {
                    calls.add(applied);
                }
            }
            case Hir.ValueInvocation call when reachable.containsKey(call.target()) ->
                    calls.add(call.target());
            case Hir.Var.Denoting named -> {
                ReachName.Declaration read = named.reachesADeclaration();
                HelperEntry entry = read == null ? null : reachable.get(read);
                if (entry != null && entry.definition().params().isEmpty()) {
                    reads.add(read);
                }
            }
            default -> { }
        }
        Hir.forEachChild(e, child -> collect(stdlib, child, reachable, calls, reads));
    }
}
