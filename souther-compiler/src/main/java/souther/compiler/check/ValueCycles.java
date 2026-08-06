package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * A value defined in terms of itself, refused before anything is expanded.
 *
 * <p>A value is substituted at each of its references (ADR-0072), so one that reaches itself is
 * substituted into itself and there is no body to reach the end of. It has to be refused before the
 * first expansion rather than caught by whatever depth guard the expansion runs into, which reports
 * a nesting the author did not write.
 *
 * <p>The value graph is not the call graph. A helper on a call cycle is lowered to a method and
 * recurses at run time (ADR-0038); a value has no such form, so a cycle that passes through one is an
 * error however it is closed — by naming a value, or by calling a helper that names it. The two are
 * reported apart: a value cycle sent through the recursion check would be told to declare a return
 * type it never wrote.
 */
public final class ValueCycles {

    private ValueCycles() {}

    /**
     * Refuses a value of {@code m} that reaches itself, or answers.
     *
     * <p>Asked of the module as it was written, before its helper parameter types are settled and
     * before any body is expanded. Settling expands the bodies it reads, so a cycle left standing
     * until then is substituted into itself there — and what comes back is a depth guard naming a
     * nesting the author did not write.
     *
     * <p>Building the edges it needs rather than taking an expansion table: what it reads is the
     * module's own definitions and what each of them calls, which is settled by nothing.
     */
    public static void rejectIn(Ast.Module m, Map<String, Ast.FnDef> published) {
        HelperTable table = HelperTable.of(m, published, InliningPolicy.FULL);
        Map<String, Set<String>> callsOf = new LinkedHashMap<>();
        for (Map.Entry<String, Ast.FnDef> e : table.own().entrySet()) {
            Set<String> called = new LinkedHashSet<>();
            HelperInliner.helperCallsIn(e.getValue().writtenBody(), table.reachable(), called);
            callsOf.put(e.getKey(), called);
        }
        reject(table.own(), callsOf);
    }

    /**
     * Refuses the first value of {@code own} that reaches itself, naming the path it goes round.
     *
     * <p>{@code callsOf} is the call graph over the same table: a cycle may be closed by calling a
     * helper that names the value, so the two kinds of edge are followed together.
     */
    static void reject(Map<String, Ast.FnDef> own, Map<String, Set<String>> callsOf) {
        Map<String, Set<String>> edges = new LinkedHashMap<>();
        for (Map.Entry<String, Ast.FnDef> e : own.entrySet()) {
            Set<String> out = new LinkedHashSet<>(callsOf.getOrDefault(e.getKey(), Set.of()));
            valuesRead(e.getValue().writtenBody(), own, out);
            edges.put(e.getKey(), out);
        }
        for (Map.Entry<String, Ast.FnDef> e : own.entrySet()) {
            if (!e.getValue().params().isEmpty()) {
                continue;   // a helper's own recursion is the call graph's business
            }
            // A value stands for a value. A block written as one — a `.field` getter, whose parameter
            // the compiler synthesizes — is refused where it is written rather than where it is used.
            //
            // Unless the definition says it is a function. Then the block is what that says it is,
            // and its parameters are the ones the written type names.
            boolean declaredAFunction = e.getValue().declaredReturn() != null
                    && e.getValue().declaredReturn().asFn() != null;
            if (!declaredAFunction && e.getValue().writtenBody() instanceof Ast.Block block) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.block.notvalue").title("check.block.title")
                                .at(block.pos()).build(),
                        "a block is not a value: `let " + e.getKey() + "` writes no parameters, so it"
                                + " defines a value, and a block cannot be one (spec 12.5)");
            }
            List<String> path = new ArrayList<>();
            if (pathBackTo(e.getKey(), e.getKey(), edges, new LinkedHashSet<>(), path)) {
                path.add(0, e.getKey());
                String written = String.join(" -> ", path);
                throw CompileException.of(
                        Diagnostic.of(null, "check.value.cycle").title("check.value.cycle.title")
                                .at(e.getValue().written().region())
                                .args(e.getKey(), written).build(),
                        "`let " + e.getKey() + "` is defined in terms of itself (" + written + ")");
            }
        }
    }

    /** The names of {@code own}'s values that {@code e} reads. A value is written bare, so a
     * reference to one is a {@code Var} and never reaches the call graph. */
    static void valuesRead(Ast.Expr e, Map<String, Ast.FnDef> own, Set<String> out) {
        if (e == null) {
            return;
        }
        if (e instanceof Ast.Var v && v.denotes() instanceof ValueName.Helper) {
            Ast.FnDef d = own.get(v.name());
            if (d != null && d.params().isEmpty()) {
                out.add(v.name());
            }
        }
        Ast.forEachChild(e, c -> valuesRead(c, own, out));
    }

    /** Records into {@code path} a route from {@code from} back to {@code target}, or answers false. */
    private static boolean pathBackTo(String from, String target, Map<String, Set<String>> edges,
                                      Set<String> seen, List<String> path) {
        for (String next : edges.getOrDefault(from, Set.of())) {
            path.add(next);
            if (next.equals(target)) {
                return true;
            }
            if (seen.add(next) && pathBackTo(next, target, edges, seen, path)) {
                return true;
            }
            path.remove(path.size() - 1);
        }
        return false;
    }
}
