package souther.compiler.core;

import souther.compiler.ast.Hir;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * A Core-to-Core pass over the tree the backend emits: a fold whose accumulator is a collection it
 * only grows builds that collection instead of rebuilding it.
 *
 * <p>{@code List.map} and {@code List.filter} are folds seeded with {@code []} whose step is
 * {@code acc ++ [f(x)]} — an immutable append per element, which shares structure but still writes a
 * new vector each time. When the step uses the accumulator nowhere but as the left side of that
 * {@code ++}, no one can see the intermediate lists, so the walk can carry a builder that fills one
 * 32-slot block at a time and seal it at the end. Every combinator derived from fold has that shape,
 * and so does a fold an author wrote the same way.
 *
 * <p>A map accumulated the same way — {@code groupBy}, {@code indexBy}, a count kept with
 * {@code upsert} — gets the same treatment, and there the step may read what it has written as well
 * as write it, since that is what {@code upsert} does. What no accumulator may do is reach anywhere
 * it could be kept, because a builder is the collection it is becoming only for as long as nobody
 * holds an earlier one.
 *
 * <p>Two such walks in a row are then joined into one: {@code map} over a {@code filter} builds the
 * filtered list only to walk it again, and since {@code fold} is the one loop the language has, the
 * shape to recognise is a single one — a build whose list is another build. The outer step takes the
 * place of the inner one's append, so the list in between is never built and the outer step is
 * applied where it stands rather than through an {@code Fn}.
 *
 * <p>It runs after the check and before emission, on {@link Core} rather than on the AST, which is
 * what keeps it out of the analyses' way: the invariant discharge, the {@code .field} desugar and the
 * helper-parameter diagnostics all read the surface tree, where a {@code List.map} is still a
 * {@code List.map}.
 *
 * <p>What joining two walks does change is <em>when</em> each step runs: unjoined, every element goes
 * through the first walk before the second starts, and joined, each element goes through both. Two
 * steps that can each abort — a construction whose invariant fails, a division by zero — therefore
 * abort on a different element than they did before. Which abort comes first is not something a
 * program may rest on (an abort is a fault, not an answer, ADR-0029), and no answer changes.
 */
public final class GrowingFold {

    /** The fold the rewrite recognises: the self-hosted walk in {@code souther.list}. */
    private static final String FOLD = "List.foldFrom";

    /** The rewritten fold: {@code $build(step, xs, from)} walks {@code xs} with a builder as the
     *  accumulator and seals it into a list. Emitted by the backend, written by nobody — so it is
     *  one of the operations this compiler emits and not a name any module reaches. */
    private static final Core.CallTarget BUILD = Core.Emitted.BUILD_LIST;

    /** The {@code acc ++ …} inside a rewritten step: it adds to the builder the walk carries and
     *  answers with it. Only ever reached from {@link #BUILD}'s step. */
    private static final Core.CallTarget GROW = Core.Emitted.GROW_LIST;

    /** The same for a fold accumulating a map: the walk carries a builder and hands over the map it
     *  built, and the step's {@code Map.insert} writes into it. */
    private static final Core.CallTarget MAP_BUILD = Core.Emitted.BUILD_MAP;

    private static final Core.CallTarget PUT = Core.Emitted.PUT_MAP;

    /** The empty map a fold accumulating one starts from, and the insert that grows it. */
    private static final String EMPTY = "Map.empty";

    private static final String INSERT = "Map.insert";

    /** What a step may do with the map it is growing besides writing to it: read it. A builder answers
     *  these from what it holds so far, which is what the fold's own step read from the version it was
     *  given, and each of them answers with a value of its own rather than with the map. Every one
     *  takes the map last, which is how the accumulator is recognised in the call. */
    private static final Set<String> READS = Set.of(
            "Map.get", "Map.containsKey", "Map.size", "Map.isEmpty",
            "Map.keys", "Map.values", "Map.toList");

    private GrowingFold() {}

    /** {@code body} with every growing fold in it rewritten, innermost first — so a {@code map} over
     *  a {@code filter} builds both, and the two builds are then joined into one. */
    public static Core rewrite(Core body) {
        Core mapped = Core.mapChildren(body, GrowingFold::rewrite, s -> s,
                nd -> Core.mapChildren(nd, GrowingFold::rewrite, s -> s));
        if (mapped instanceof Core.Call call) {
            Core built = built(call);
            if (built != null) {
                mapped = built;
            }
        }
        if (mapped instanceof Core.Call call && call.fn() == BUILD) {
            Core joined = joined(call);
            if (joined != null) {
                return joined;
            }
        }
        if (mapped instanceof Core.LetIn li) {
            Core joined = joinedThroughBinding(li);
            if (joined != null) {
                return joined;
            }
        }
        return mapped;
    }

    /**
     * The same join, where the list in between is reached through the binding that expanding
     * {@code List.map} left behind: a helper's argument becomes a {@code let}, so
     * {@code map(f, filter(p, xs))} arrives as {@code let ys = <the filter> in <the map over ys>}
     * rather than as one call inside the other. Null when it is not that.
     *
     * <p>The binding the two walks met through is dropped, and whatever bindings the inner walk
     * needed are kept, now standing over the joined walk. They are evaluated where they were, so the
     * only thing that could go wrong is one of their names meaning something else inside the outer
     * step — which is checked for rather than reasoned about.
     */
    private static Core joinedThroughBinding(Core.LetIn binding) {
        if (!(binding.body() instanceof Core.Call outer) || outer.fn() != BUILD
                || !(outer.args().get(1) instanceof Core.Read walked)
                || !walked.binding().equals(binding.binder().id())
                || uses(binding.body(), binding.binder().id()) != 1) {
            return null;
        }
        List<Core.LetIn> kept = new ArrayList<>();
        Core value = binding.value();
        while (value instanceof Core.LetIn nested) {
            kept.add(nested);
            value = nested.body();
        }
        if (!(value instanceof Core.Call inner) || inner.fn() != BUILD) {
            return null;
        }
        for (Core.LetIn k : kept) {
            if (uses(outer.args().get(0), k.binder().id()) > 0) {
                return null;
            }
        }
        Core joined = joined(new Core.Call(BUILD,
                List.of(outer.args().get(0), inner, outer.args().get(2)),
                outer.type(), outer.pos()));
        if (joined == null) {
            return null;
        }
        for (int i = kept.size() - 1; i >= 0; i--) {
            Core.LetIn k = kept.get(i);
            joined = new Core.LetIn(k.binder(), k.value(), joined, joined.type(), k.pos());
        }
        return joined;
    }

    /** {@code call} as a build, or null when it is not a fold that only grows a list or a map. */
    private static Core built(Core.Call call) {
        if (!call.name().equals(FOLD) || call.args().size() != 4) {
            return null;
        }
        Core seed = call.args().get(1);
        Core.CallTarget build;
        Core step;
        if (call.type() instanceof Type.ListOf
                && seed instanceof Core.ListLit lit && lit.elements().isEmpty()) {
            build = BUILD;
            step = grownStep(call.args().get(0));
        } else if (call.type() instanceof Type.MapOf
                && seed instanceof Core.Call empty && empty.name().equals(EMPTY)) {
            build = MAP_BUILD;
            step = puttingStep(call.args().get(0));
        } else {
            return null;   // the walk starts from something already holding entries
        }
        if (step == null) {
            return null;
        }
        return new Core.Call(build, List.of(step, call.args().get(2), call.args().get(3)),
                call.type(), call.pos());
    }

    /**
     * The step of a fold accumulating a map, with its inserts turned into writes, or null when the
     * step does anything else with the accumulator.
     *
     * <p>Reading the accumulator is allowed here, where growing a list allows nothing but the append:
     * {@code Map.updateOrInsert} is an insert whose value comes from looking the key up first, and a builder
     * answers a lookup with what it holds. What is refused is the accumulator reaching anywhere it
     * could be kept — stored as a value, handed to a function, answered with as something other than
     * the map being grown — because a builder is only the map it is becoming for as long as nobody
     * holds an earlier one.
     */
    private static Core puttingStep(Core step) {
        if (step instanceof Core.LetIn li) {
            Core inner = puttingStep(li.body());
            return inner == null ? null : new Core.LetIn(li.binder(), li.value(), inner,
                    li.type(), li.pos());
        }
        if (!(step instanceof Core.Block block) || block.params().size() != 2) {
            return null;
        }
        Set<BindingId> acc = aliases(block.body(), block.params().get(0));
        int[] found = {0};
        Core putting = answers(block.body(), acc, found, GrowingFold::inserted);
        if (putting == null
                || found[0] + reads(block.body(), acc) + aliased(block.body(), acc)
                        != mentions(block.body(), acc)) {
            return null;
        }
        return new Core.Block(block.params(), putting, block.type(), block.pos());
    }

    /**
     * The names that stand for the accumulator inside a step: the step's own parameter, and every
     * name a {@code let} binds to one of them.
     *
     * <p>Expanding a helper is what makes this necessary. {@code Map.updateOrInsert(k, d, f, acc)} becomes its
     * body with each argument bound by a {@code let}, so the map the inserts name is not {@code acc}
     * but the {@code let} that was given it — one name for one value, which is what the walk needs to
     * see through. A binding of a binding is followed the same way, so the set is closed rather than
     * one level deep.
     */
    private static Set<BindingId> aliases(Core body, Hir.Binder acc) {
        Set<BindingId> names = new LinkedHashSet<>();
        names.add(acc.id());
        int before;
        do {
            before = names.size();
            count(body, e -> {
                if (e instanceof Core.LetIn li && li.value() instanceof Core.Read v
                        && names.contains(v.binding())) {
                    names.add(li.binder().id());
                }
                return false;
            }, new int[1]);
        } while (names.size() > before);
        return names;
    }

    /** How many times one of {@code acc}'s bindings is reached anywhere in {@code e}. */
    private static int mentions(Core e, Set<BindingId> acc) {
        int n = 0;
        for (BindingId binding : acc) {
            n += uses(e, binding);
        }
        return n;
    }

    /** How many times the accumulator is read as a map rather than written to — the {@code Map.get} of
     *  an {@code upsert}, a {@code containsKey} guarding an insert. Each of those is one of the
     *  mentions {@link #puttingStep} counts, and a mention that is none of the three refuses the walk. */
    private static int reads(Core e, Set<BindingId> acc) {
        int[] n = {0};
        count(e, c -> c instanceof Core.Call call && READS.contains(call.name())
                && !call.args().isEmpty()
                && call.args().getLast() instanceof Core.Read v && acc.contains(v.binding()), n);
        return n[0];
    }

    /** How many times the accumulator is mentioned as the value another name is bound to — the
     *  mentions {@link #aliases} followed. */
    private static int aliased(Core e, Set<BindingId> acc) {
        int[] n = {0};
        count(e, c -> c instanceof Core.LetIn li && li.value() instanceof Core.Read v
                && acc.contains(v.binding()), n);
        return n[0];
    }

    /**
     * {@code build(outer, build(inner, xs, from), 0)} as one walk over {@code xs}, or null when the
     * two do not join.
     *
     * <p>The join puts the outer step where the inner one adds to its builder: what the inner walk
     * would have handed to the list in between goes straight to the outer step, and the builder the
     * outer step grows is the only one left. Chained walks join a pair at a time, the innermost first,
     * because the result is again a build whose step adds to a builder.
     *
     * <p>Three things must hold. The outer walk starts at the head, or it would skip elements of a
     * list that is no longer there to count. The inner step adds in exactly one place, so the outer
     * step is moved rather than copied — a copy would duplicate whatever lambdas it holds. And what
     * the inner step adds is one element, since the outer step takes an element and there is no loop
     * here to take a list apart with.
     */
    private static Core joined(Core.Call build) {
        if (!(build.args().get(2) instanceof Core.Int from) || from.value() != 0) {
            return null;
        }
        if (!(build.args().get(1) instanceof Core.Call inner) || inner.fn() != BUILD) {
            return null;
        }
        if (!(build.args().get(0) instanceof Core.Block outer) || outer.params().size() != 2
                || !(inner.args().get(0) instanceof Core.Block innerStep)) {
            return null;
        }
        if (adds(innerStep.body()) != 1) {
            return null;
        }
        boolean[] refused = {false};
        Core body = piped(innerStep.body(), outer, refused);
        if (refused[0]) {
            return null;
        }
        Core step = new Core.Block(innerStep.params(), body, innerStep.type(), innerStep.pos());
        return new Core.Call(BUILD, List.of(step, inner.args().get(1), inner.args().get(2)),
                build.type(), build.pos());
    }

    /** How many places {@code e} adds to the builder of the walk it is the step of. A nested walk's
     *  step is another walk's business, so this stops at a block. */
    private static int adds(Core e) {
        if (e instanceof Core.Block) {
            return 0;
        }
        int[] n = {e instanceof Core.Call c && c.fn() == GROW ? 1 : 0};
        Core.forEachChild(e, child -> n[0] += adds(child));
        return n[0];
    }

    /** {@code e} with the one add in it replaced by {@code outer} applied there: the accumulator the
     *  add was given becomes the outer step's accumulator and the element it added becomes the outer
     *  step's element, both bound rather than substituted, so a name the two steps happen to share
     *  reads the value it was given here. */
    private static Core piped(Core e, Core.Block outer, boolean[] refused) {
        if (refused[0] || e instanceof Core.Block) {
            return e;
        }
        if (e instanceof Core.Call c && c.fn() == GROW) {
            if (!(c.args().get(1) instanceof Core.ListLit lit) || lit.elements().size() != 1) {
                refused[0] = true;   // the add hands over a list, and the outer step takes an element
                return e;
            }
            Core body = outer.body();
            Core element = new Core.LetIn(outer.params().get(1), lit.elements().get(0), body,
                    body.type(), c.pos());
            return new Core.LetIn(outer.params().get(0), c.args().get(0), element,
                    body.type(), c.pos());
        }
        return Core.mapChildren(e, child -> piped(child, outer, refused), s -> s,
                nd -> Core.mapChildren(nd, child -> piped(child, outer, refused), s -> s));
    }

    /** The step with its appends turned into adds, or null when the step does something else with the
     *  accumulator. A {@code let} the checker put around the step binds a captured value and is kept
     *  where it stands. */
    private static Core grownStep(Core step) {
        if (step instanceof Core.LetIn li) {
            Core inner = grownStep(li.body());
            return inner == null ? null : new Core.LetIn(li.binder(), li.value(), inner,
                    li.type(), li.pos());
        }
        if (!(step instanceof Core.Block block) || block.params().size() != 2) {
            return null;
        }
        Set<BindingId> acc = aliases(block.body(), block.params().get(0));
        int[] found = {0};
        Core grown = answers(block.body(), acc, found, GrowingFold::appended);
        if (grown == null || found[0] + aliased(block.body(), acc) != mentions(block.body(), acc)) {
            // Every mention of the accumulator must be one of the appends found above. One more and
            // the list is read as a value somewhere — its length, an element, the answer itself —
            // and a builder is not that list yet.
            return null;
        }
        return new Core.Block(block.params(), grown, block.type(), block.pos());
    }

    /** What an answering position of a growing step may hold besides the accumulator itself: the one
     *  operation that grows it, rewritten to the one that writes into the builder. Null refuses. */
    private interface Growth {
        Core at(Core e, Set<BindingId> acc);
    }

    /** {@code acc ++ rhs} as an add to the builder. */
    private static Core appended(Core e, Set<BindingId> acc) {
        if (!(e instanceof Core.Binary b) || b.op() != Hir.BinOp.CONCAT
                || !(b.left() instanceof Core.Read v) || !acc.contains(v.binding())) {
            return null;
        }
        return new Core.Call(GROW, List.of(b.left(), b.right()), b.type(), b.pos());
    }

    /** {@code Map.insert(key, value, acc)} as a write into the builder. */
    private static Core inserted(Core e, Set<BindingId> acc) {
        if (!(e instanceof Core.Call c) || !c.name().equals(INSERT) || c.args().size() != 3
                || !(c.args().get(2) instanceof Core.Read v) || !acc.contains(v.binding())) {
            return null;
        }
        return new Core.Call(PUT, List.of(c.args().get(2), c.args().get(0), c.args().get(1)),
                c.type(), c.pos());
    }

    /**
     * {@code e}, a position the step's answer comes from, with the accumulator's growth rewritten to
     * a write; null when some position answers with anything other than the accumulator or a growth
     * of it.
     *
     * <p>Only the answering positions are walked. A condition, a scrutinee or a bound value is
     * ordinary code the rewrite leaves alone — what matters is what the accumulator does there, which
     * the counts in {@link #grownStep} and {@link #puttingStep} settle.
     */
    private static Core answers(Core e, Set<BindingId> acc, int[] found, Growth growth) {
        switch (e) {
            case Core.Read v -> {
                if (!acc.contains(v.binding())) {
                    return null;
                }
                found[0]++;
                return v;
            }
            case Core.If iff -> {
                Core then = answers(iff.then(), acc, found, growth);
                Core els = then == null ? null : answers(iff.els(), acc, found, growth);
                return els == null ? null
                        : new Core.If(iff.cond(), then, els, iff.origin(), iff.type(), iff.pos());
            }
            case Core.LetIn li -> {
                if (acc.contains(li.binder().id()) && !(li.value() instanceof Core.Read v
                        && acc.contains(v.binding()))) {
                    return null;   // one of the accumulator's names now stands for something else
                }
                Core body = answers(li.body(), acc, found, growth);
                return body == null ? null
                        : new Core.LetIn(li.binder(), li.value(), body, li.type(), li.pos());
            }
            case Core.Match m -> {
                List<Core.Case> cases = new ArrayList<>();
                for (Core.Case c : m.cases()) {
                    if (c.binding() != null && acc.contains(c.binding().id())) {
                        return null;
                    }
                    Core body = answers(c.body(), acc, found, growth);
                    if (body == null) {
                        return null;
                    }
                    cases.add(new Core.Case(c.caseTypes(), c.binding(), body, c.bindType(), c.pos()));
                }
                return new Core.Match(m.scrutinee(), cases, m.origin(), m.type(), m.pos());
            }
            // A call a representation kept standing is not part of the tree a fold grows in: this
            // reads what the backend emits, and that keeps none.
            case Core.PreservedCall p -> throw p.unexpectedIn("fold growing");
            default -> {
                Core grown = growth.at(e, acc);
                if (grown != null) {
                    found[0]++;
                }
                return grown;
            }
        }
    }

    /**
     * How many times {@code binding} is reached anywhere in {@code e} — read as a value, applied, or
     * spread.
     *
     * <p>All three are one node: reading a value, applying one and spreading one each hold a
     * {@link Core.Read} saying which binding it is, so a binding of the same spelling further in is
     * not one of these and there is one thing to count. Undercounting is what this must not do: the
     * rewrite is allowed when every way the accumulator is reached is one of the growths found, so a
     * way that went uncounted would let it through.
     */
    private static int uses(Core e, BindingId binding) {
        int[] n = {0};
        count(e, node -> node instanceof Core.Read v && v.binding().equals(binding), n);
        return n[0];
    }

    /** How many nodes anywhere in {@code e} answer {@code holds}. */
    private static void count(Core e, java.util.function.Predicate<Core> holds, int[] n) {
        if (holds.test(e)) {
            n[0]++;
        }
        Core.forEachChild(e, child -> count(child, holds, n));
    }
}
