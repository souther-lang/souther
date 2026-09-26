package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.types.ValueName;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.SequencedSet;
import java.util.Set;

/**
 * The {@code let}s a module hands to the modules that read it: the helpers its invariants and its
 * {@code ensures} clauses call, and the definitions it publishes, each with what it reaches.
 *
 * <p>An invariant is part of what a type is, so it has to be readable where the type is imported,
 * and it cannot be read without the helpers it names. A published value or helper is the same: a
 * value's body is read by the analyses of the reader and a helper is expanded where it is called, so
 * a reader needs the body, and the body's own workings with it. A {@code let} none of them reaches
 * is not handed over — a module hands over what its declarations need, not its implementation.
 *
 * <p>One answer, read by what a jar carries and by what a module offers other modules to copy. Each
 * working it out for itself would agree only until one of them was edited, and a definition carried
 * and not offered is one a reader copies with nothing to hold the copy to.
 */
public final class CarriedDefinitions {

    private CarriedDefinitions() {}

    /**
     * What {@code resolved} hands over, by the name each definition is declared under, in the order
     * they are reached.
     *
     * @param published what the module publishes
     */
    public static SequencedSet<String> of(Hir.Module resolved, Set<String> published) {
        // A behavior's body is not published — a reader has its signature and calls it — so a
        // behavior's own `let` is not among what may be carried, whatever reaches its spelling.
        Set<String> behaviorNames = new LinkedHashSet<>();
        for (Hir.BehaviorDef b : resolved.behaviors()) {
            behaviorNames.add(b.name());
        }
        // What may be carried is what the model declares. The resolved module is wider than that:
        // an attached file's values join the module its rows join, and an attached file does not
        // add to what the model compiles to — so a `let` only it declares has no source here to
        // carry. Asked of the definition, which is where that is recorded.
        Map<String, Hir.FnDef> own = new LinkedHashMap<>();
        for (Hir.FnDef fn : resolved.fns()) {
            if (HelperInliner.isHelperName(behaviorNames, fn.name()) && fn.role().isTheModels()) {
                own.put(fn.name(), fn);
            }
        }

        SequencedSet<String> reached = new LinkedHashSet<>();
        for (Hir.Def def : resolved.defs()) {
            if (def instanceof Hir.Data d) {
                for (Hir.InvariantClause clause : d.invariants()) {
                    reach(clause.expr(), own, reached);
                }
            }
        }
        for (Hir.BehaviorDef behavior : resolved.behaviors()) {
            if (behavior instanceof Hir.SpecBehavior spec) {
                for (Hir.EnsuresClause clause : spec.ensures()) {
                    for (Hir.EnsuresArm arm : clause.arms()) {
                        reach(arm.expr(), own, reached);
                    }
                }
            }
        }
        for (Hir.FnDef fn : own.values()) {
            if (published.contains(fn.name()) && fn.body() instanceof Hir.FnBody.Written w) {
                reached.add(fn.name());
                reach(w.expr(), own, reached);
            }
        }
        return Collections.unmodifiableSequencedSet(reached);
    }

    /**
     * A helper is reached by being called and by being named — handing one to a combinator, as in
     * {@code all(positive, items)}, needs it just as much as calling it does.
     *
     * <p>One set does for both visited and reached: a helper is added the first time it is seen, and
     * nothing is ever taken out, so a second sighting stops the walk by itself.
     */
    private static void reach(Hir.Expr e, Map<String, Hir.FnDef> own, Set<String> reached) {
        // What a name reaches, read off the name rather than off its spelling. A clause is written
        // among bindings — a data's fields, a behavior's parameters, `value` — and one of those
        // spelled like a helper is not a use of that helper. Answered by spelling, a parameter
        // called `positive` carried the module's `positive` across the boundary, and one called
        // like a behavior carried that behavior's implementation.
        String named = e instanceof Hir.Var.Denoting var
                && var.denotes() instanceof ValueName.Helper helper ? helper.name() : null;
        if (named != null && own.containsKey(named) && reached.add(named)) {
            // an `intrinsic` helper is a name with nothing to walk into
            if (own.get(named).body() instanceof Hir.FnBody.Written w) {
                reach(w.expr(), own, reached);
            }
        }
        Hir.forEachChild(e, c -> reach(c, own, reached));
    }
}
