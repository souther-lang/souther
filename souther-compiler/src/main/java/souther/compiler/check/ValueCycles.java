package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.msg.NameMessage;
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
 * <p>A value is substituted at each of its references, so one that reaches itself is substituted into
 * itself and there is no body to reach the end of. It is refused here, of the module, before anything
 * expands a body of it: the report belongs at the declaration, said once, naming the path the value
 * goes round.
 *
 * <p>The expansion refuses to substitute a value into itself as well ({@link ExpansionCycle}), and
 * that is a different statement. It bounds an algorithm handed an input this refusal rules out; it is
 * not an answer about the program, and it does not see a value that reaches itself through a helper
 * whose call it leaves standing. Neither stands in for the other.
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
    public static void rejectIn(Hir.Module m, Map<String, Hir.FnDef> published) {
        HelperTable table = HelperTable.of(m, published, InliningPolicy.FULL);
        // What the module declared, which is what a value cycle is about: a value written in terms of
        // itself is a defect in what the author wrote, and a helper the module only took on to emit
        // was written by somebody else and answered for there.
        Map<String, Hir.FnDef> declared = table.declarations();
        Map<String, Set<String>> callsOf = new LinkedHashMap<>();
        for (Map.Entry<String, Hir.FnDef> e : declared.entrySet()) {
            Set<String> called = new LinkedHashSet<>();
            HelperInliner.helperCallsIn(e.getValue().writtenBody(), table.reachable(), called);
            callsOf.put(e.getKey(), called);
        }
        reject(declared, callsOf);
    }

    /**
     * Refuses the first value of {@code own} that reaches itself, naming the path it goes round.
     *
     * <p>{@code callsOf} is the call graph over the same table: a cycle may be closed by calling a
     * helper that names the value, so the two kinds of edge are followed together — which is why both
     * are keyed by the name a reference reaches its target by, and neither by a spelling.
     */
    static void reject(Map<String, Hir.FnDef> own, Map<String, Set<String>> callsOf) {
        Map<String, Set<String>> edges = new LinkedHashMap<>();
        for (Map.Entry<String, Hir.FnDef> e : own.entrySet()) {
            Set<String> out = new LinkedHashSet<>(callsOf.getOrDefault(e.getKey(), Set.of()));
            valuesRead(e.getValue().writtenBody(), own, out);
            edges.put(e.getKey(), out);
        }
        // Which names lie on a cycle, worked out once over the whole graph. What is asked of each
        // value below is whether it reaches itself, and a search per value answers it by walking
        // everything that value reaches — over a chain of values that is the chain again per link.
        // The path a report names is still found by the search below, which runs for the one value
        // that is refused and for no other.
        Set<String> reachesItself = onACycle(edges);
        for (Map.Entry<String, Hir.FnDef> e : own.entrySet()) {
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
            if (!declaredAFunction && e.getValue().writtenBody() instanceof Hir.Block block) {
                throw CompileException.of(Diagnostic
                                .at(block.pos()).say(new NameMessage.ABlockIsNotAValue()).build());
            }
            if (!reachesItself.contains(e.getKey())) {
                continue;
            }
            List<String> path = new ArrayList<>();
            if (pathBackTo(e.getKey(), e.getKey(), edges, new LinkedHashSet<>(), path)) {
                path.add(0, e.getKey());
                String written = String.join(" -> ", path);
                throw CompileException.of(Diagnostic
                                .at(e.getValue().written().region())
                                .say(new NameMessage.AValueReachesItself(e.getKey(), written)).build());
            }
        }
    }

    /**
     * The values of {@code reachable} that {@code e} reads, by the name it reaches each of them by. A
     * value is written bare, so a reference to one is a {@code Var} and never reaches the call graph.
     *
     * <p>Asked with the reach name the reference carries, which is what {@link
     * HelperInliner#helperCallsIn} asks a call with. The two are the two kinds of edge in one graph
     * and are followed together, so a table answering one of them under a key the other does not use
     * is a graph with edges missing — and missing silently, because a miss is what a table does with
     * a key it has not got. Reading {@link Hir.Var#name()} here asked with the spelling instead, and
     * an import may let a name go without its qualifier: it agreed with the key only where a pass had
     * already written the spelling out qualified.
     */
    static void valuesRead(Hir.Expr e, Map<String, Hir.FnDef> reachable, Set<String> out) {
        if (e == null) {
            return;
        }
        if (e instanceof Hir.Var.Denoting v && v.denotes() instanceof ValueName.Helper) {
            Hir.FnDef d = reachable.get(v.reaches());
            if (d != null && d.params().isEmpty()) {
                out.add(v.reaches());
            }
        }
        Hir.forEachChild(e, c -> valuesRead(c, reachable, out));
    }

    /**
     * The names of {@code edges} that reach themselves: the ones in a strongly connected group of
     * more than one, and the ones with an edge to themselves.
     *
     * <p>Tarjan's, written with its own stack rather than the call stack. A module's definitions
     * nest as deeply as they are chained, and this walk is over the same chain that made the walk
     * worth doing — a recursive one would answer by running out of stack on the input it was added
     * for.
     */
    private static Set<String> onACycle(Map<String, Set<String>> edges) {
        Map<String, Integer> index = new LinkedHashMap<>();
        Map<String, Integer> low = new LinkedHashMap<>();
        Set<String> open = new LinkedHashSet<>();       // on the component stack
        List<String> component = new ArrayList<>();
        Set<String> found = new LinkedHashSet<>();
        int next = 0;
        for (String root : edges.keySet()) {
            if (index.containsKey(root)) {
                continue;
            }
            List<Walking> frames = new ArrayList<>();
            frames.add(new Walking(root, edges.getOrDefault(root, Set.of()).iterator()));
            index.put(root, next);
            low.put(root, next++);
            open.add(root);
            component.add(root);
            while (!frames.isEmpty()) {
                Walking frame = frames.get(frames.size() - 1);
                String at = frame.node();
                if (frame.edges().hasNext()) {
                    String to = frame.edges().next();
                    if (!index.containsKey(to)) {
                        index.put(to, next);
                        low.put(to, next++);
                        open.add(to);
                        component.add(to);
                        frames.add(new Walking(to, edges.getOrDefault(to, Set.of()).iterator()));
                    } else if (open.contains(to)) {
                        low.put(at, Math.min(low.get(at), index.get(to)));
                    }
                    continue;
                }
                frames.remove(frames.size() - 1);
                if (!frames.isEmpty()) {
                    String under = frames.get(frames.size() - 1).node();
                    low.put(under, Math.min(low.get(under), low.get(at)));
                }
                if (low.get(at).equals(index.get(at))) {
                    List<String> group = new ArrayList<>();
                    String popped;
                    do {
                        popped = component.remove(component.size() - 1);
                        open.remove(popped);
                        group.add(popped);
                    } while (!popped.equals(at));
                    // One name is a group of its own unless it names itself: a group of one has no
                    // way round except an edge back to where it started.
                    if (group.size() > 1 || edges.getOrDefault(at, Set.of()).contains(at)) {
                        found.addAll(group);
                    }
                }
            }
        }
        return found;
    }

    /**
     * A node the walk is inside, and the edges of it that are left.
     *
     * <p>The iterator is the frame's, taken once when the frame is pushed. A frame is resumed once
     * per edge it has, so a frame that worked out where it had got to would read the node's edges
     * once per edge — which over a name that reaches many is that name's edges squared, and a chain
     * says nothing about it because every name there reaches one.
     */
    private record Walking(String node, java.util.Iterator<String> edges) {}

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
