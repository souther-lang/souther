package souther.compiler.coverage;

import souther.compiler.ast.Hir;
import souther.compiler.types.BindingId;
import souther.compiler.types.CoverageOrigin;
import souther.compiler.types.ValueName;

import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

/**
 * Who owns the rule a fork decides by, read off the declaration that wrote the fork.
 *
 * <p>A helper spliced into a body twice writes one fork, and covering its arms through the second
 * call site establishes nothing the first did not — so its copies are one thing to cover. That holds
 * while the helper decides for itself. It stops holding where the caller hands the decision in: the
 * arms of {@code List.filter} are decided by whatever predicate this call site supplied, and two
 * calls supplying two predicates are two rules, neither of them exercised by a row through the
 * other.
 *
 * <p>Which of the two a fork is, is written in the declaration. A parameter of function type is the
 * caller handing in a rule; a parameter of any other type is the caller handing in data for the
 * declaration's own rule to read. {@code atLeast(18, x)} and {@code atLeast(65, y)} are one fork
 * deciding one way about two numbers, and {@code decide(b: Bool)} is one fork however many bodies
 * call it — the argument is not the rule.
 *
 * <p>So this is a fact about a declaration and not about a tree that ran. Worked out from the shape
 * of a condition after expansion instead, the two are not tellable apart at all: the argument has
 * been substituted in either case, and what is left is one expression that says nothing about who
 * decided. Keyed by {@link CoverageOrigin}, which the front end mints once per construct and every
 * copy carries.
 */
public record DecisionSources(Map<CoverageOrigin, DecisionSource> byFork) {

    /** Nothing read, which is what a reading with no declarations to walk comes to. */
    public static final DecisionSources NONE = new DecisionSources(Map.of());

    public DecisionSources {
        byFork = Map.copyOf(byFork);
    }

    /**
     * Who decides at {@code fork}.
     *
     * <p>{@link DecisionSource.Own} where nothing was read about it. A fork this walk never reached
     * is one no declaration it was handed wrote, and what a caller does with an unknown fork is
     * treat its copies as one — which is the answer that was given before any of this was read, and
     * the one that asks an author for no row they do not owe.
     */
    public DecisionSource at(CoverageOrigin fork) {
        DecisionSource said = byFork.get(fork);
        return said == null ? DecisionSource.OWN : said;
    }

    /** What {@code declarations} say about the forks they write. */
    public static DecisionSources of(Collection<Hir.FnDef> declarations) {
        Map<CoverageOrigin, DecisionSource> byFork = new LinkedHashMap<>();
        for (Hir.FnDef fn : declarations) {
            read(fn, byFork);
        }
        return byFork.isEmpty() ? NONE : new DecisionSources(byFork);
    }

    private static void read(Hir.FnDef fn, Map<CoverageOrigin, DecisionSource> out) {
        Map<BindingId, String> rules = new LinkedHashMap<>();
        for (Hir.FnParam param : fn.params()) {
            // A parameter of function type, and no other. What the caller hands to one is the rule
            // this body decides by; what it hands to the rest is what that rule reads.
            if (param.type() != null && param.type().asFn() != null
                    && param.binder() != null && param.binder().binding() != null) {
                rules.put(param.binder().binding(), param.name());
            }
        }
        if (!(fn.body() instanceof Hir.FnBody.Written written)) {
            return;
        }
        forks(written.expr(), rules, out);
    }

    private static void forks(Hir.Expr e, Map<BindingId, String> rules,
                              Map<CoverageOrigin, DecisionSource> out) {
        if (e instanceof Hir.If iff) {
            Set<String> supplied = new LinkedHashSet<>();
            applied(iff.cond(), rules, supplied);
            // Written down whichever it came to. A fork with an entry saying `Own` is one this walk
            // reached and read; one with no entry is one it never saw, and the two are answered
            // alike by design rather than by both being absent.
            out.putIfAbsent(iff.origin(), supplied.isEmpty() ? DecisionSource.OWN
                    : new DecisionSource.Supplied(new LinkedHashSet<>(supplied)));
        }
        Hir.forEachChild(e, child -> forks(child, rules, out));
    }

    /** Which of {@code rules} the expression applies, anywhere inside it. */
    private static void applied(Hir.Expr e, Map<BindingId, String> rules, Set<String> out) {
        if (e instanceof Hir.Apply call && call.function() instanceof Hir.Var.Denoting named
                && named.denotes() instanceof ValueName.Local local) {
            String parameter = rules.get(local.id());
            if (parameter != null) {
                out.add(parameter);
            }
        }
        Hir.forEachChild(e, child -> applied(child, rules, out));
    }
}
