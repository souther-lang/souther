package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.core.Core;
import souther.compiler.coverage.ControlPointId;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.reach.PathDecision;
import souther.compiler.reach.Proof;
import souther.compiler.reach.Reachability;
import souther.compiler.reach.WhyUnsettled;
import souther.compiler.types.BindingId;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * What the model's own rules say arrives at each place in a behavior's body.
 *
 * <p>The reading the invariant-discharge check already makes, answered as a fact instead of
 * consumed as a step. That check threads what holds where it stands and returns at a place the
 * conditions cannot all hold — which is exactly the question every measure asks about an arm, and
 * every measure was answering it again from the declarations alone, with no way to know what the
 * guards above had established. Two guards on one position left the second one's departure owed a
 * row that nothing can write.
 *
 * <p>Held by {@link ControlPointId} and not by probe number. An arm answering {@code unreachable}
 * has no probe, and it is the arm a claim is about.
 *
 * <p><b>Only a proof excludes, and nothing here proves that something arrives.</b> A state the
 * domains found no contradiction in is a state they had nothing to say about, so this answers
 * {@link Reachability.Unsettled} there rather than {@link Reachability.Reachable} — what earns the
 * latter is a run, or a rule that settles the question completely, and neither is read here.
 *
 * <p>A place this walk did not get to is absent, which {@link Answers#at} reads as unsettled. That
 * is the fail-open direction and it is the one that costs nothing: an obligation stays owed and
 * nothing is reported.
 */
public final class PathReachability {

    /** What was found, and what a place nothing was found about comes to. */
    public record Answers(Map<ControlPointId, Reachability> found) {

        public static final Answers NONE = new Answers(Map.of());

        public Answers {
            found = Map.copyOf(found);
        }

        /**
         * What arrives at {@code where}.
         *
         * <p>A place this reading has nothing filed under is one the walk did not get to, which is
         * an answer and not a gap: it is {@link WhyUnsettled.TheWalkDidNotReachIt}, and every
         * consumer treats it as it treats any other unsettled place.
         */
        public Reachability at(ControlPointId where) {
            Reachability answer = found.get(where);
            return answer != null ? answer
                    : Reachability.notSettled(new WhyUnsettled.TheWalkDidNotReachIt());
        }
    }

    /**
     * The places of one behavior's body, read against what its declared inputs guarantee.
     *
     * <p>The bindings are the implementation's own and the types are the declaration's, paired by
     * position and stopping at the business parameters — which is the rule the check that types the
     * body reads them by, asked here rather than worked out a second way. A trailing parameter
     * stands for a behavior this one depends on and guarantees nothing about a value.
     */
    public static Answers of(Core body, Hir.SpecBehavior spec, Hir.FnDef fn,
                             CoverageSites.Plan plan, Symbols symbols) {
        if (fn == null || spec == null) {
            return Answers.NONE;
        }
        Scope params = Scope.NONE;
        for (int i = 0; i < spec.params().size() && i < fn.params().size(); i++) {
            params = params.with(fn.params().get(i).binder(),
                    TypeOps.successType(spec.params().get(i).type()));
        }
        return of(body, params, plan, symbols);
    }

    /**
     * The same, told the bindings outright.
     *
     * <p>Fail-open throughout. A condition of a shape the rules have no word for narrows nothing,
     * so the arms under it come out unsettled rather than proven either way; a walk that falls over
     * answers about what it had reached and no more.
     */
    public static Answers of(Core body, Scope params, CoverageSites.Plan plan, Symbols symbols) {
        if (body == null || plan.isEmpty()) {
            return Answers.NONE;
        }
        PathEngine engine = new PathEngine(symbols, Map.of());
        Map<ControlPointId, Reachability> out = new LinkedHashMap<>();
        try {
            PathEngine.Entered in = PathEngine.Entered.nothing();
            for (Map.Entry<BindingId, Scope.Binding> p : params.bindings().entrySet()) {
                in = engine.enter(new Core.Read(p.getValue().name(), p.getKey(),
                        p.getValue().type(), body.pos()), in.known(), in.at());
            }
            new PathReachability(engine, plan, out)
                    .walk(body, in.known(), in.at(), List.of());
        } catch (RuntimeException why) {
            // The run-time check is the backstop for the analysis this borrows, and it is the
            // backstop for this too: what was not read leaves an obligation standing.
            InvariantChecker.gaveUp("reachability", why);
        }
        return new Answers(out);
    }

    private final PathEngine engine;
    private final CoverageSites.Plan plan;
    private final Map<ControlPointId, Reachability> out;

    private PathReachability(PathEngine engine, CoverageSites.Plan plan,
                             Map<ControlPointId, Reachability> out) {
        this.engine = engine;
        this.plan = plan;
        this.out = out;
    }

    /**
     * Reads {@code e} under what holds where it stands.
     *
     * <p>{@code decided} is the conditions taken in on the way here, in the order they were
     * assumed. Carried rather than recovered from where a place sits, because what a proof is
     * allowed to name is what the domains were actually given: a condition of a shape nothing could
     * take in narrowed nothing and is not on the list.
     */
    private void walk(Core e, Known k, Denotations at, List<PathDecision> decided) {
        if (e == null || k.reachesNothing()) {
            // Nothing stands here, so nothing below is a place anything arrives at either. The arm
            // that made it so was answered where it was entered; the arms under it are left absent,
            // which reads as unsettled — the outermost one is the place to say it, and saying it
            // again at every fork inside would be the same finding several times over.
            return;
        }
        switch (e) {
            case Core.If iff -> {
                walk(iff.cond(), k, at, decided);
                ControlPointId.ArmOccurrence[] arms = plan.armsOf(iff);
                enterArm(arms, 0, iff, iff.then(), k, at, decided, true);
                enterArm(arms, 1, iff, iff.els(), k, at, decided, false);
            }
            case Core.LetIn li -> {
                walk(li.value(), k, at, decided);
                PathEngine.Entered in = engine.bindLet(li, k, at);
                walk(li.body(), in.known(), in.at(), decided);
            }
            default -> {
                Core.forEachChild(e, child -> walk(child, k, at, decided));
            }
        }
    }

    /**
     * One arm of a fork, read under its own side of the condition.
     *
     * <p>The answer is filed at the arm and the walk goes on inside it. Where the condition leaves
     * nothing, the arm is proven and what is under it is not walked: everything there is unreachable
     * for the same reason, and one finding is what an author is owed.
     */
    private void enterArm(ControlPointId.ArmOccurrence[] arms, int index, Core.If iff, Core arm,
                          Known k, Denotations at, List<PathDecision> decided, boolean holds) {
        Known inside = engine.assuming(iff.cond(), k, at, holds);
        List<PathDecision> under = new ArrayList<>(decided);
        under.add(new PathDecision(iff.cond().pos(), holds));
        if (arms != null && index < arms.length) {
            out.put(arms[index], inside.reachesNothing()
                    ? new Reachability.Unreachable(new Proof.ConflictingPathConditions(under))
                    : Reachability.notSettled(new WhyUnsettled.NoWitness()));
        }
        walk(arm, inside, at, under);
    }
}
