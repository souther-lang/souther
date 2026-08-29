package souther.compiler.coverage;

import souther.compiler.ast.Hir;
import souther.compiler.types.BindingId;
import souther.compiler.types.ReachName;
import souther.compiler.types.ValueName;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

/**
 * Which of a declaration's arguments the value it answers with depends on.
 *
 * <p>Of every parameter and not of the ones a reader happens to care about. Whether an argument
 * reaches the answer is a question about the flow of values and has nothing to do with what is
 * being carried: {@code relay(b: Bool) = b} answers out of its argument as surely as
 * {@code apply(p, x) = p(x)} does, and a reading that only followed the parameters of function type
 * would step over the first. What was being followed and what is worth following are two questions,
 * and joining them meant a rule reaching a fork through a plain {@code Bool} was not followed at
 * all — so two call sites' rules were counted as one, and one nothing exercised was reported as
 * covered.
 *
 * <p>Taken to a fixed point rather than in an order, so nothing here has to know which declaration
 * calls which. Every declaration being read starts at resting on nothing, and a pass reads each of
 * them against what the others have come to so far; the walk runs until nothing moves. A recursive
 * helper is read like any other and takes as many passes as its own answer needs, which is why it is
 * not stopped after a number of passes worked out from how many declarations there are.
 *
 * <p>Starting at nothing is what makes the answer the same whatever order the declarations are
 * written in. Started at nothing known — which is what a callable this never reads is — a call to
 * something declared below would be read as resting on every argument on the first pass, and there
 * is no pass that takes it back.
 */
public record AnswerDependencies(Map<ReachName.Declaration, Set<Integer>> bySlot) {

    /** Nothing read. */
    public static final AnswerDependencies NONE = new AnswerDependencies(Map.of());

    public AnswerDependencies {
        Map<ReachName.Declaration, Set<Integer>> copy = new LinkedHashMap<>();
        bySlot.forEach((name, slots) -> copy.put(name, Set.copyOf(slots)));
        bySlot = Map.copyOf(copy);
    }

    /**
     * Which of {@code declaration}'s arguments its answer depends on, or null where nothing here
     * says.
     *
     * <p>Null and not empty. Nothing said is not the same as nothing depended on, and folded
     * together the second swallows the first: a call this never read — one the language implements
     * rather than writes, one written as sugar over another, one reached through a name — was
     * answered "this call rests on none of its arguments", and a rule reaching a fork through it
     * was not followed at all. Which is a rule two call sites wrote counted as one.
     */
    public Set<Integer> of(ReachName.Declaration declaration) {
        return bySlot.get(declaration);
    }

    /** What {@code declarations} answer out of. */
    public static AnswerDependencies of(Map<ReachName.Declaration, Hir.FnDef> declarations) {
        // Everything being read starts at nothing, so a declaration this has not got to yet is
        // told from a callable it will never read. Started from an empty map, the two were the same
        // absence: a call to something declared further down was read as resting on every argument,
        // and the passes only ever add — so the answer stayed at what the first pass could not
        // know, and forks resting on nothing were owed a row per call site.
        Map<ReachName.Declaration, Set<Integer>> bySlot = new LinkedHashMap<>();
        declarations.keySet().forEach(each -> bySlot.put(each, Set.of()));
        boolean moved = true;
        while (moved) {
            moved = false;
            for (Map.Entry<ReachName.Declaration, Hir.FnDef> each : declarations.entrySet()) {
                Set<Integer> was = bySlot.get(each.getKey());
                Set<Integer> now = answeredOutOf(each.getValue(), bySlot);
                if (!now.equals(was)) {
                    bySlot.put(each.getKey(), Set.copyOf(now));
                    moved = true;
                }
            }
        }
        return bySlot.isEmpty() ? NONE : new AnswerDependencies(bySlot);
    }

    private static Set<Integer> answeredOutOf(Hir.FnDef fn, Map<ReachName.Declaration, Set<Integer>> bySlot) {
        if (!(fn.body() instanceof Hir.FnBody.Written written)) {
            return Set.of();
        }
        Map<BindingId, Integer> params = new LinkedHashMap<>();
        for (int slot = 0; slot < fn.params().size(); slot++) {
            Hir.FnParam param = fn.params().get(slot);
            if (param.binder() != null && param.binder().binding() != null) {
                params.put(param.binder().binding(), slot);
            }
        }
        Set<Integer> out = new LinkedHashSet<>();
        dependsOn(written.expr(), params, bySlot, new LinkedHashMap<>(), NamedCallables.NONE, out);
        return out;
    }

    /**
     * Which of {@code params} the value of {@code e} depends on.
     *
     * <p>Written apart from the reading of what a fork rests on, which asks the narrower question of
     * whether a rule reaches it. This one is about values reaching values and knows nothing about
     * rules; the other projects this onto the parameters that carry one.
     */
    static void dependsOn(Hir.Expr e, Map<BindingId, Integer> params,
                          Map<ReachName.Declaration, Set<Integer>> bySlot, Map<BindingId, Set<Integer>> bound,
                          NamedCallables named, Set<Integer> out) {
        switch (e) {
            case Hir.Var.Denoting read when read.denotes() instanceof ValueName.Local local -> {
                Integer slot = params.get(local.id());
                if (slot != null) {
                    out.add(slot);
                }
                Set<Integer> held = bound.get(local.id());
                if (held != null) {
                    out.addAll(held);
                }
            }
            case Hir.LetIn let when let.binder() != null && let.binder().binding() != null -> {
                Set<Integer> holds = new LinkedHashSet<>();
                dependsOn(let.value(), params, bySlot, bound, named, holds);
                Map<BindingId, Set<Integer>> wider = new LinkedHashMap<>(bound);
                wider.put(let.binder().binding(), holds);
                dependsOn(let.body(), params, bySlot, wider,
                        named.and(let.binder().binding(), let.value()), out);
                return;
            }
            // A call through a name is a call to whatever that name was bound to, which is what
            // says who answers for it. Read as a call to a declaration of the name itself, nothing
            // answers, and every argument is read for want of anything better.
            case Hir.Apply call when call.function() instanceof Hir.Var.Denoting callee -> {
                // Only the arguments the callee answers out of. One it never reads is not something
                // this call's value depends on, whatever else that argument would decide elsewhere.
                ReachName.Declaration reaches = named.reached(callee);
                Set<Integer> uses = reaches == null ? null : bySlot.get(reaches);
                for (int i = 0; i < call.args().size(); i++) {
                    // Every argument where nothing says which of them this call rests on. What is
                    // lost by reading one it does not is a value said to reach further than it
                    // does; what is lost the other way is a value that reaches and is not followed.
                    if (uses == null || uses.contains(i)) {
                        dependsOn(call.args().get(i), params, bySlot, bound, named, out);
                    }
                }
                // And what is being applied. Applying a parameter is answering out of it, and a
                // reading that only followed the arguments called a helper that applies what it was
                // handed a helper that answers out of nothing.
                dependsOn(call.function(), params, bySlot, bound, named, out);
                return;
            }
            default -> { }
        }
        Hir.forEachChild(e, child -> dependsOn(child, params, bySlot, bound, named, out));
    }
}
