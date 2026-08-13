package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.types.BindingId;
import souther.compiler.types.ValueName;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.msg.BehaviorMessage;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Checks that recursion is total by default (spec §fn-declaration): a module-own recursive helper
 * that is not {@code partial} must terminate, proven by <em>size-change termination</em> (Lee–Jones–
 * Ben-Amram) over the structural sub-term order. Every recursive call is a size-change graph relating
 * caller parameters to callee arguments: an argument that is a strictly smaller part of a parameter
 * (a sub-term from a {@code match} on a field or a case, or a value handed to a container combinator's
 * closure — a list element, or an {@code Option}'s unwrapped payload) is a strict ({@code <}) arc; an
 * argument passed through unchanged is a non-increasing
 * ({@code =}) arc. Composing these graphs to a fixpoint, the recursion terminates iff every idempotent
 * cycle carries a strictly decreasing parameter. Self-referential data is finite by construction (the
 * inhabitability check), so a proven descent bottoms out — the helper terminates, and its examples can
 * be evaluated at compile time.
 *
 * <p>This subsumes self-recursion (a group of one) and mutual recursion (a strongly-connected group)
 * in one analysis; it accepts strictly more than a single-decreasing-position check, e.g. structural
 * lexicographic recursion. A {@code partial} helper opts out (it is not checked and may not terminate);
 * if any member of a mutually-recursive group is {@code partial} the whole group is skipped — a cycle
 * through an unchecked member cannot be certified, so its other members are not independently certified
 * either. The stdlib's {@code List.foldFrom} (index recursion) is trusted total and exempt — only the
 * helpers this module declared are checked, whatever else it emits beside them. Numeric
 * ({@code n - 1}) and index ({@code i + 1}) recursion are not structural (Souther has no inductive
 * {@code Nat}) and must be {@code partial}.
 */
final class TotalityChecker {

    /** The composition-closure of a group's size-change graphs is bounded above by the number of
     * distinct labeled graphs, which grows with parameter count; a group of many-parameter helpers
     * could otherwise blow up the worklist and hang the check. When the closure exceeds this many
     * graphs the group is rejected as too complex to prove total (conservative — sound, not accepted). */
    private static final int MAX_CLOSURE = 50_000;

    private TotalityChecker() {}

    /** Checks every non-{@code partial}, module-own recursive helper (or group) for size-change
     * termination. */
    static void check(HelperInliner inliner) {
        Map<String, Ast.FnDef> own = inliner.held();
        Map<String, Set<String>> ownEdges = ownCallGraph(own);
        Set<String> handled = new HashSet<>();
        for (String name : inliner.recursiveHelpers()) {
            Ast.FnDef h = own.get(name);
            // Only what this module declared is checked. A recursive helper it took on to emit — a
            // prelude `List.foldFrom`, one another module published — carries its declaring module's
            // guarantee (ADR-0098), and its own module proved it. Asked of the declaration: the name
            // it is reached by here says nothing about who wrote it, and `List.foldFrom` does not
            // even hold the module it came from.
            if (h == null || !h.declaredBy(inliner.moduleName())) {
                continue;
            }
            Set<String> group = cycleMembers(name, ownEdges);   // the strongly-connected group (>= 1)
            if (!handled.add(name)) {
                continue;   // a sibling of an already-analyzed group
            }
            handled.addAll(group);
            // `partial` opts out; a `partial` anywhere in a mutual group opts the whole group out.
            if (group.stream().anyMatch(m -> own.get(m).partial())) {
                continue;
            }
            Built built = buildScgs(group, own);
            Set<Scg> closure = close(built.scgs());
            if (closure == null) {
                throw tooComplex(group, own);
            }
            if (isSizeChangeTerminating(closure)) {
                continue;
            }
            throw notTerminating(group, own, built.firstCall());
        }
    }

    /** The rejection for a group that is not size-change terminating. A group of one keeps the
     * structural-recursion message, reported at a representative self-call; a larger group reports the
     * mutual failure at its lexicographically-first member (a stable anchor). */
    private static CompileException notTerminating(Set<String> group, Map<String, Ast.FnDef> own,
                                                   Map<String, Ast.Apply> firstCall) {
        if (group.size() == 1) {
            String name = group.iterator().next();
            Ast.FnDef h = own.get(name);
            String message = "recursive helper `let " + name + "` is not structurally recursive: `" + name
                    + "(...)` passes no argument that is a strictly smaller part of a parameter."
                    + " Recurse on a part obtained by `match` (a field or a case), count with"
                    + " `fold`, or mark the helper `partial`";
            Ast.Apply at = firstCall.get(name);
            return at == null
                    ? error(h, new BehaviorMessage.NotStructurallyRecursive(name))
                    : error(at, new BehaviorMessage.NotStructurallyRecursive(name));
        }
        Ast.FnDef anchor = own.get(java.util.Collections.min(group));
        String members = backtickJoin(group);
        return error(anchor, new BehaviorMessage.NotSizeChangeTerminating(members));
    }

    /** The rejection for a group whose size-change closure exceeds {@link #MAX_CLOSURE}: it may or may
     * not terminate, but it is too complex to decide, so it is rejected conservatively. */
    private static CompileException tooComplex(Set<String> group, Map<String, Ast.FnDef> own) {
        Ast.FnDef anchor = own.get(java.util.Collections.min(group));
        String members = backtickJoin(group);
        return error(anchor, new BehaviorMessage.TooComplexToProveTotal(members));
    }

    // --- size-change graphs -------------------------------------------------

    /** A size-change arc label: {@code LT} is a strict ({@code <}) decrease, {@code EQ} is
     * non-increasing ({@code =}); a {@code null} cell is an unknown relation (no arc). */
    private enum Rel { LT, EQ }

    /** The size-change graph of one call edge {@code from -> to}: {@code m[i][j]} relates parameter
     * {@code i} of the caller to argument position {@code j} (parameter {@code j}) of the callee.
     * Equality is by value over {@code from}, {@code to}, and the matrix — required, since the closure
     * lives in a {@code HashSet} and idempotence is tested with {@code equals}. */
    private static final class Scg {
        final String from;
        final String to;
        final Rel[][] m;

        Scg(String from, String to, Rel[][] m) {
            this.from = from;
            this.to = to;
            this.m = m;
        }

        @Override
        public boolean equals(Object o) {
            if (!(o instanceof Scg other)) {
                return false;
            }
            return from.equals(other.from) && to.equals(other.to) && Arrays.deepEquals(m, other.m);
        }

        @Override
        public int hashCode() {
            return (from.hashCode() * 31 + to.hashCode()) * 31 + Arrays.deepHashCode(m);
        }
    }

    /** The size-change graphs of a group, plus a representative self/mutual call per member (its
     * source position for a rejection message — recorded here so the reject path need not re-walk). */
    private record Built(List<Scg> scgs, Map<String, Ast.Apply> firstCall) {}

    /** Builds the per-call-edge size-change graphs for every member of {@code group}. */
    private static Built buildScgs(Set<String> group, Map<String, Ast.FnDef> own) {
        List<Scg> scgs = new ArrayList<>();
        Map<String, Ast.Apply> firstCall = new HashMap<>();
        for (String f : group) {
            Ast.FnDef def = own.get(f);
            List<Ast.FnParam> params = def.params();
            // which bindings the parameters are, not what they are spelled: a `let` inside the
             // body may write a parameter's name, and it is another value
            Set<BindingId> paramNames = new HashSet<>();
            Map<BindingId, Integer> idxOf = new HashMap<>();
            for (int i = 0; i < params.size(); i++) {
                paramNames.add(params.get(i).binder().id());
                idxOf.put(params.get(i).binder().id(), i);
            }
            List<RecCall> calls = new ArrayList<>();
            walk(def.writtenBody(), group, paramNames, Map.of(), Map.of(), calls);
            for (RecCall rc : calls) {
                firstCall.putIfAbsent(f, rc.call());
                int toArity = own.get(rc.callee()).params().size();
                Rel[][] m = new Rel[params.size()][toArity];
                int cols = Math.min(toArity, rc.call().args().size());
                for (int j = 0; j < cols; j++) {
                    Ast.Expr arg = rc.call().args().get(j);
                    Set<BindingId> strict = strictSmaller(arg, rc.lt(), rc.eq(), paramNames);
                    Set<BindingId> root = rootParams(arg, rc.lt(), rc.eq(), paramNames);
                    for (BindingId p : strict) {
                        m[idxOf.get(p)][j] = Rel.LT;
                    }
                    for (BindingId p : root) {
                        if (!strict.contains(p) && m[idxOf.get(p)][j] == null) {
                            m[idxOf.get(p)][j] = Rel.EQ;
                        }
                    }
                }
                scgs.add(new Scg(f, rc.callee(), m));
            }
        }
        return new Built(scgs, firstCall);
    }

    /** Relational composition {@code a;b} ({@code a.to == b.from}): an arc {@code i -> k} is {@code LT}
     * if some middle {@code j} carries a strict arc on either side, else {@code EQ} if some {@code j}
     * carries two {@code EQ} arcs, else absent. */
    private static Scg compose(Scg a, Scg b) {
        int rows = a.m.length;
        int cols = b.m.length > 0 ? b.m[0].length : 0;
        int mid = a.m.length > 0 ? a.m[0].length : 0;
        Rel[][] r = new Rel[rows][cols];
        for (int i = 0; i < rows; i++) {
            for (int k = 0; k < cols; k++) {
                Rel best = null;
                for (int j = 0; j < mid && j < b.m.length; j++) {
                    Rel aj = a.m[i][j];
                    Rel bj = b.m[j][k];
                    if (aj == null || bj == null) {
                        continue;
                    }
                    if (aj == Rel.LT || bj == Rel.LT) {
                        best = Rel.LT;
                        break;
                    }
                    best = Rel.EQ;
                }
                r[i][k] = best;
            }
        }
        return new Scg(a.from, b.to, r);
    }

    /** Closes {@code base} under composition to a fixpoint, or returns {@code null} if the closure
     * exceeds {@link #MAX_CLOSURE} (the group is then rejected as too complex — never accepted unproven).
     * Finite otherwise: the arcs range over a two-element label set on fixed dimensions and
     * {@code from}/{@code to} over a finite group, so only finitely many distinct graphs exist. */
    private static Set<Scg> close(List<Scg> base) {
        Set<Scg> all = new HashSet<>(base);
        java.util.Deque<Scg> work = new java.util.ArrayDeque<>(base);
        while (!work.isEmpty()) {
            if (all.size() > MAX_CLOSURE) {
                return null;
            }
            Scg x = work.poll();
            for (Scg y : new ArrayList<>(all)) {
                if (x.to.equals(y.from)) {
                    Scg c = compose(x, y);
                    if (all.add(c)) {
                        work.add(c);
                    }
                }
                if (y.to.equals(x.from)) {
                    Scg c = compose(y, x);
                    if (all.add(c)) {
                        work.add(c);
                    }
                }
            }
        }
        return all;
    }

    /** The Lee–Jones–Ben-Amram criterion: the group terminates iff every idempotent self-loop in the
     * closure carries a strictly decreasing parameter (a diagonal {@code LT}). An unknown relation is
     * no arc, so acceptance always rests on a proven descent — a non-terminating helper is never
     * accepted. */
    private static boolean isSizeChangeTerminating(Set<Scg> closure) {
        for (Scg g : closure) {
            if (!g.from.equals(g.to) || !compose(g, g).equals(g)) {
                continue;   // only idempotent self-loops witness a cycle
            }
            boolean strictDiagonal = false;
            for (int i = 0; i < g.m.length; i++) {
                if (i < g.m[i].length && g.m[i][i] == Rel.LT) {
                    strictDiagonal = true;
                    break;
                }
            }
            if (!strictDiagonal) {
                return false;
            }
        }
        return true;
    }

    /** A recorded recursive call to a group member, with the callee and the smaller-than / equal-to
     * relations ({@code lt} / {@code eq}) in scope where it appears. */
    private record RecCall(String callee, Ast.Apply call,
                           Map<BindingId, Set<BindingId>> lt,
                           Map<BindingId, Set<BindingId>> eq) {}

    /**
     * Walks {@code e}, threading {@code lt} (each local -&gt; the parameters it is a strictly smaller
     * part of) and {@code eq} (each local -&gt; the parameters it is exactly equal to, e.g. a {@code let}
     * alias), and records every call to a member of {@code group}. A {@code match} case binding is a
     * strictly smaller part of the parameters the scrutinee is rooted at; a {@code let} carries the
     * strict or equal relation of its value forward.
     */
    private static void walk(Ast.Expr e, Set<String> group, Set<BindingId> paramNames,
                             Map<BindingId, Set<BindingId>> lt, Map<BindingId, Set<BindingId>> eq,
                             List<RecCall> calls) {
        switch (e) {
            case Ast.Match m -> {
                walk(m.scrutinee(), group, paramNames, lt, eq, calls);
                Set<BindingId> rooted = rootParams(m.scrutinee(), lt, eq, paramNames);
                for (Ast.Case c : m.cases()) {
                    Map<BindingId, Set<BindingId>> inner = lt;
                    if (c.binding() != null && !rooted.isEmpty()) {
                        inner = with(lt, c.binding().id(), rooted);   // the bound value is smaller than each root
                    }
                    walk(c.body(), group, paramNames, inner, eq, calls);
                }
            }
            case Ast.LetIn li -> {
                walk(li.value(), group, paramNames, lt, eq, calls);
                Set<BindingId> smaller = strictSmaller(li.value(), lt, eq, paramNames);
                Set<BindingId> equal = eqRoots(li.value(), eq, paramNames);
                Map<BindingId, Set<BindingId>> ltInner =
                        smaller.isEmpty() ? lt : with(lt, li.binder().id(), smaller);
                Map<BindingId, Set<BindingId>> eqInner =
                        equal.isEmpty() ? eq : with(eq, li.binder().id(), equal);
                walk(li.body(), group, paramNames, ltInner, eqInner, calls);
            }
            case Ast.Apply call -> {
                if (group.contains(call.reaches())) {
                    calls.add(new RecCall(call.written(), call, lt, eq));
                }
                Combinators.Written handed = Combinators.handedTo(call);
                for (Ast.Expr arg : call.args()) {
                    // The closure is asked by identity: a call may write one expression twice, and
                    // only the argument the operation applies is the one an element arrives in.
                    if (handed == null || arg != handed.step()) {
                        walk(arg, group, paramNames, lt, eq, calls);
                        continue;
                    }
                    // The step consumes the container argument; each value it is handed (a list
                    // element, a map's value, or an option's unwrapped payload) is a sub-term of that
                    // container, so if the container is (part of) a parameter, the value is a strictly
                    // smaller part of it. Bind the element parameter accordingly for the step body. An
                    // operation the library states no such thing of is treated as handing its closure
                    // nothing, which rejects a recursion rather than wrongly accepting one; a
                    // freshly-constructed container (`Some(p)`) roots at no parameter, so its payload
                    // is not credited as smaller either.
                    Set<BindingId> elemRoots = rootParams(handed.container(), lt, eq, paramNames);
                    Map<BindingId, Set<BindingId>> inner = elemRoots.isEmpty()
                            ? lt
                            : with(lt, handed.element().id(), elemRoots);
                    walk(handed.step().body(), group, paramNames, inner, eq, calls);
                }
            }
            default -> forEachChild(e, child -> walk(child, group, paramNames, lt, eq, calls));
        }
    }

    /** The parameters {@code e} is a (possibly-improper) descendant of — a parameter itself, an exact
     * alias of one (through {@code eq}), a field chain rooted at one, or a local already known to be
     * smaller than one. Used for a {@code match} scrutinee: unwrapping a case of such a value yields a
     * strictly smaller part. */
    private static Set<BindingId> rootParams(Ast.Expr e, Map<BindingId, Set<BindingId>> lt,
                                          Map<BindingId, Set<BindingId>> eq, Set<BindingId> paramNames) {
        return switch (e) {
            case Ast.Var v when v.denotes() instanceof ValueName.Local local -> {
                Set<BindingId> s = new HashSet<>();
                if (paramNames.contains(local.id())) {
                    s.add(local.id());
                }
                s.addAll(lt.getOrDefault(local.id(), Set.of()));
                s.addAll(eq.getOrDefault(local.id(), Set.of()));
                yield s;
            }
            case Ast.FieldAccess fa -> rootParams(fa.target(), lt, eq, paramNames);
            default -> Set.of();
        };
    }

    /** The parameters {@code e} is a <em>strictly</em> smaller part of — a field access (a field is
     * strictly smaller than its target), or a local already known to be smaller. A bare parameter, or
     * an exact alias of one, is not strictly smaller than itself. */
    private static Set<BindingId> strictSmaller(Ast.Expr e, Map<BindingId, Set<BindingId>> lt,
                                             Map<BindingId, Set<BindingId>> eq, Set<BindingId> paramNames) {
        return switch (e) {
            case Ast.Var v when v.denotes() instanceof ValueName.Local local ->
                    lt.getOrDefault(local.id(), Set.of());
            case Ast.FieldAccess fa -> rootParams(fa.target(), lt, eq, paramNames);
            default -> Set.of();
        };
    }

    /** The parameters {@code e} is <em>exactly equal</em> to — a bare parameter or an alias of one. A
     * field access is strictly smaller, not equal, so it is not here (it is in {@link #strictSmaller}). */
    private static Set<BindingId> eqRoots(Ast.Expr e, Map<BindingId, Set<BindingId>> eq,
                                          Set<BindingId> paramNames) {
        if (e instanceof Ast.Var v && v.denotes() instanceof ValueName.Local local) {
            Set<BindingId> s = new HashSet<>();
            if (paramNames.contains(local.id())) {
                s.add(local.id());
            }
            s.addAll(eq.getOrDefault(local.id(), Set.of()));
            return s;
        }
        return Set.of();
    }

    private static Map<BindingId, Set<BindingId>> with(Map<BindingId, Set<BindingId>> env,
                                                       BindingId binding, Set<BindingId> params) {
        Map<BindingId, Set<BindingId>> copy = new HashMap<>(env);
        copy.put(binding, params);
        return copy;
    }

    private static String backtickJoin(Set<String> names) {
        List<String> sorted = new ArrayList<>(names);
        java.util.Collections.sort(sorted);
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < sorted.size(); i++) {
            if (i > 0) {
                sb.append(", ");
            }
            sb.append('`').append(sorted.get(i)).append('`');
        }
        return sb.toString();
    }

    // --- call graph over module-own helpers (for grouping mutual recursion) ---

    private static Map<String, Set<String>> ownCallGraph(Map<String, Ast.FnDef> own) {
        Map<String, Set<String>> edges = new HashMap<>();
        for (Ast.FnDef h : own.values()) {
            Set<String> called = new HashSet<>();
            collectOwnCalls(h.writtenBody(), own.keySet(), called);
            edges.put(h.name(), called);
        }
        return edges;
    }

    private static void collectOwnCalls(Ast.Expr e, Set<String> own, Set<String> out) {
        if (e instanceof Ast.Apply call && call.function() instanceof Ast.Var.Denoting
                && own.contains(call.reaches())) {
            out.add(call.written());
        }
        forEachChild(e, c -> collectOwnCalls(c, own, out));
    }

    /** The helpers on {@code name}'s recursive cycle: those reachable from {@code name} that also reach
     * {@code name} back. Includes {@code name} when it is (self- or mutually-) recursive. */
    private static Set<String> cycleMembers(String name, Map<String, Set<String>> edges) {
        Set<String> forward = reachable(name, edges);
        Set<String> cycle = new HashSet<>();
        for (String m : forward) {
            if (reachable(m, edges).contains(name)) {
                cycle.add(m);
            }
        }
        return cycle;
    }

    private static Set<String> reachable(String from, Map<String, Set<String>> edges) {
        Set<String> seen = new HashSet<>();
        java.util.Deque<String> work = new java.util.ArrayDeque<>(edges.getOrDefault(from, Set.of()));
        while (!work.isEmpty()) {
            String n = work.poll();
            if (seen.add(n)) {
                work.addAll(edges.getOrDefault(n, Set.of()));
            }
        }
        return seen;
    }

    /** Said at the helper's own name: `let` comes first, and a report anchored at the definition
     *  underlines the keyword rather than what it is about. */
    private static <M extends souther.compiler.diag.msg.Message & souther.compiler.diag.msg.Reported>
            CompileException error(Ast.FnDef h, M said) {
        return CompileException.of(Diagnostic.at(h.written().reportedAt()).say(said).build());
    }

    private static <M extends souther.compiler.diag.msg.Message & souther.compiler.diag.msg.Reported>
            CompileException error(Ast.Apply call, M said) {
        return CompileException.of(Diagnostic.at(call.appliedAt()).say(said).build());
    }

    // --- a direct-child visitor mirroring the one in HelperInliner/TypeChecker ---

    /** Applies {@code f} to every direct subexpression of {@code e}; the one exhaustive walk
     * lives on the AST, so a node kind added later cannot be skipped here unnoticed. */
    private static void forEachChild(Ast.Expr e, java.util.function.Consumer<Ast.Expr> f) {
        Ast.forEachChild(e, f);
    }
}
