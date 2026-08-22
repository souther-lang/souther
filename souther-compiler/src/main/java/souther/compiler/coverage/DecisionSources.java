package souther.compiler.coverage;

import souther.compiler.ast.Hir;
import souther.compiler.types.BindingId;
import souther.compiler.types.CoverageOrigin;
import souther.compiler.types.ValueName;

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
 * arms of {@code List.filter} are decided by whatever rule this call site supplied, and two calls
 * supplying two rules are two rules, neither of them exercised by a row through the other.
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
 *
 * <p><b>What a condition rests on, and not what it applies.</b> A fork depending on a rule it was
 * handed need not apply it: the rule can be given a name and applied under that, or handed to
 * another helper whose answer the fork tests. Asked as "does this condition apply a function
 * parameter", both of those come back as the declaration deciding for itself, and the rules two call
 * sites supplied are counted as one — which is a rule nothing exercised reported as covered. So the
 * question is asked of the whole condition and followed through the bindings it reads and the
 * helpers it calls. Helpers are not recursive, so following them ends.
 */
public record DecisionSources(Map<CoverageOrigin, DecisionSource> byFork, boolean read) {

    /**
     * No reading was taken.
     *
     * <p>Told from a reading that was taken and found nothing, which is what a module with no forks
     * comes to. A caller handed this one has no declarations behind it and gets the answer that was
     * given before any of this was read: copies of a fork are one thing to cover. A caller handed a
     * reading that was taken gets refused where it holds no entry, because there the absence is the
     * bookkeeping having missed a fork rather than there being nothing to say.
     */
    public static final DecisionSources NONE = new DecisionSources(Map.of(), false);

    public DecisionSources(Map<CoverageOrigin, DecisionSource> byFork) {
        this(byFork, true);
    }

    public DecisionSources {
        byFork = Map.copyOf(byFork);
    }

    /**
     * Who decides at {@code fork}.
     *
     * <p>Refused where nothing was read about it. Both answers are written down, so having no
     * entry is not one of them: it says this reading never saw the fork, which is a fact about the
     * bookkeeping and not about the model. Answered {@code Own} instead, every copy of a fork the
     * caller decides would be counted as one — the very thing this exists to stop — and the day a
     * lowering makes a fork out of something new, it would go on being counted that way with
     * nothing saying so.
     */
    public DecisionSource at(CoverageOrigin fork) {
        DecisionSource said = byFork.get(fork);
        if (said == null && !read) {
            return DecisionSource.OWN;
        }
        if (said == null) {
            throw new IllegalStateException("no declaration this reading was handed wrote " + fork
                    + "; a fork the arms are counted at is one whose decision somebody owns, and"
                    + " answering that nobody does counts every copy of it as one");
        }
        return said;
    }

    /**
     * What {@code declarations} say about the forks they write, keyed the way a call reaches them.
     *
     * <p>Read in two passes because one declaration's forks can rest on another's answer. The first
     * settles which arguments each declaration answers out of ({@link AnswerDependencies}); the
     * second reads the forks with those summaries in hand, and projects them onto the parameters
     * that carry a rule.
     */
    public static DecisionSources of(Map<String, Hir.FnDef> reachable, Hir.FnDef... own) {
        Map<String, Hir.FnDef> declarations = new LinkedHashMap<>(reachable);
        for (Hir.FnDef each : own) {
            if (each != null) {
                declarations.put(each.name(), each);
            }
        }
        AnswerDependencies answersOn = AnswerDependencies.of(declarations);
        Map<CoverageOrigin, DecisionSource> byFork = new LinkedHashMap<>();
        for (Hir.FnDef fn : declarations.values()) {
            forks(fn, answersOn, byFork);
        }
        return new DecisionSources(byFork);
    }

    private static void forks(Hir.FnDef fn, AnswerDependencies answersOn,
                              Map<CoverageOrigin, DecisionSource> out) {
        if (!(fn.body() instanceof Hir.FnBody.Written written)) {
            return;
        }
        forks(written.expr(), Rules.of(fn), answersOn, new LinkedHashMap<>(), out);
    }

    /**
     * Every fork {@code e} writes, under the names in force where each of them stands.
     *
     * <p>Carried down rather than taken again at the fork. A rule bound to a name a line above the
     * fork that reads it is in force there and nowhere in the condition, so a reading that started
     * afresh at each fork found the name and not what it stands for — and called a fork the caller
     * decides the declaration's own.
     */
    private static void forks(Hir.Expr e, Rules rules, AnswerDependencies answersOn,
                              Map<BindingId, Set<String>> bound,
                              Map<CoverageOrigin, DecisionSource> out) {
        switch (e) {
            case Hir.If iff -> said(iff.origin(), iff.cond(), rules, answersOn, bound, out);
            // Every construct that bears arms, and by what settles which arm is taken. A `match`
            // decides by its subject as an `if` decides by its condition, and a construction that
            // may fail by the value it is given — so a rule the caller supplied reaches all three
            // the same way. Left out, the arms of a `match` over a rule the caller wrote were one
            // obligation however many rules were handed in.
            case Hir.Match match ->
                    said(match.origin(), match.scrutinee(), rules, answersOn, bound, out);
            case Hir.IfConstructed made ->
                    said(made.origin(), made.construct(), rules, answersOn, bound, out);
            // The guards of a comprehension are forks of the lowering rather than of the source, and
            // the lowering runs after the rule has been substituted in. Read here, where the rule is
            // still a parameter: read afterwards, a guard resting on a rule the caller supplied is a
            // fork nothing wrote and every copy of it is counted as one.
            case Hir.ListComp comp -> {
                for (int i = 0; i < comp.guards().size(); i++) {
                    said(comp.origin().lowered(i), comp.guards().get(i), rules, answersOn, bound,
                            out);
                }
            }
            case Hir.LetIn let when let.binder() != null && let.binder().binding() != null -> {
                Set<String> holds = new LinkedHashSet<>();
                rules.restsOn(let.value(), answersOn, bound, holds);
                forks(let.value(), rules, answersOn, bound, out);
                Map<BindingId, Set<String>> wider = new LinkedHashMap<>(bound);
                wider.put(let.binder().binding(), holds);
                forks(let.body(), rules, answersOn, wider, out);
                return;
            }
            default -> { }
        }
        Hir.forEachChild(e, child -> forks(child, rules, answersOn, bound, out));
    }

    private static void said(CoverageOrigin fork, Hir.Expr cond, Rules rules,
                             AnswerDependencies answersOn,
                             Map<BindingId, Set<String>> bound,
                             Map<CoverageOrigin, DecisionSource> out) {
        Set<String> on = new LinkedHashSet<>();
        rules.restsOn(cond, answersOn, bound, on);
        out.putIfAbsent(fork, on.isEmpty() ? DecisionSource.OWN : new DecisionSource.Supplied(on));
    }

    /** The rules one declaration was handed: its function parameters, by binding and by place. */
    private record Rules(Map<BindingId, String> byBinding, java.util.List<String> inOrder) {

        static Rules of(Hir.FnDef fn) {
            Map<BindingId, String> byBinding = new LinkedHashMap<>();
            java.util.List<String> inOrder = new java.util.ArrayList<>();
            for (Hir.FnParam param : fn.params()) {
                inOrder.add(param.name());
                // A parameter of function type, and no other. What the caller hands to one is the
                // rule this body decides by; what it hands to the rest is what that rule reads.
                if (param.type() != null && param.type().asFn() != null
                        && param.binder() != null && param.binder().binding() != null) {
                    byBinding.put(param.binder().binding(), param.name());
                }
            }
            return new Rules(byBinding, inOrder);
        }

        /**
         * Which of these rules the value of {@code e} rests on.
         *
         * <p>Three ways a value can rest on one, and a reading short of all three calls a call
         * site's rule the declaration's own. It applies it; or it reads a name the rule was bound
         * to, which is followed; or it hands the rule to a helper whose answer it uses, which is
         * followed through that helper's own summary.
         */
        void restsOn(Hir.Expr e, AnswerDependencies answersOn,
                     Map<BindingId, Set<String>> bound, Set<String> out) {
            switch (e) {
                case Hir.Var.Denoting named when named.denotes() instanceof ValueName.Local local -> {
                    String rule = byBinding.get(local.id());
                    if (rule != null) {
                        out.add(rule);
                    }
                    Set<String> held = bound.get(local.id());
                    if (held != null) {
                        out.addAll(held);
                    }
                }
                case Hir.LetIn let when let.binder() != null && let.binder().binding() != null -> {
                    Set<String> holds = new LinkedHashSet<>();
                    restsOn(let.value(), answersOn, bound, holds);
                    Map<BindingId, Set<String>> wider = new LinkedHashMap<>(bound);
                    wider.put(let.binder().binding(), holds);
                    restsOn(let.body(), answersOn, wider, out);
                    return;
                }
                case Hir.Apply call when call.function() instanceof Hir.Var.Denoting callee -> {
                    Set<Integer> uses = answersOn.of(callee.reaches());
                    for (int i = 0; i < call.args().size(); i++) {
                        // Only the arguments the callee's answer rests on. An argument it never
                        // reads decides nothing about what this call comes to, whatever the rule
                        // inside it would decide somewhere else — read for what it holds, a rule
                        // wrapped in a lambda and handed to a helper that ignores it made every copy
                        // of the fork above its own obligation.
                        if (uses.contains(i)) {
                            restsOn(call.args().get(i), answersOn, bound, out);
                        }
                    }
                    restsOn(call.function(), answersOn, bound, out);
                    return;
                }
                default -> { }
            }
            Hir.forEachChild(e, child -> restsOn(child, answersOn, bound, out));
        }
    }
}
