package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.coverage.ControlPointId;
import souther.compiler.inputs.Admits;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.TermPath;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.reach.PathDecision;
import souther.compiler.reach.Proof;
import souther.compiler.reach.Reachability;
import souther.compiler.reach.Witness;
import souther.compiler.reach.WhyUnsettled;
import souther.compiler.types.BindingId;
import souther.compiler.types.TypeSymbol;

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
            // The order the walk found them in. `Map.copyOf` is unordered and its iteration is
            // salted per run, so the warnings read off this came out in a different order on every
            // JVM — a diagnostic whose place in the output is not a function of the source.
            found = java.util.Collections.unmodifiableMap(new LinkedHashMap<>(found));
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

        /**
         * What arrives at the comparison recorded at {@code probe}, coming out {@code result}.
         *
         * <p>Asked by probe because that is what a line read off a comparison carries. The place is
         * still the control point — this only finds it.
         */
        public Reachability atComparison(int probe, boolean result) {
            for (Map.Entry<ControlPointId, Reachability> each : found.entrySet()) {
                if (each.getKey() instanceof ControlPointId.ComparisonOutcome outcome
                        && outcome.comparisonProbe() == probe && outcome.result() == result) {
                    return each.getValue();
                }
            }
            return Reachability.notSettled(new WhyUnsettled.TheWalkDidNotReachIt());
        }

        /**
         * These answers with what the rows actually did taken in, and the proofs they took back.
         *
         * <p>A row that went through an arm went through it. So a run is a witness — the plainest
         * of them — and it settles an arm this reading had proven nothing arrives at: what happened
         * happened, and the proof was wrong rather than the row. Both come out of one act because
         * neither is derivable from the other afterwards: the corrected answers no longer say which
         * arms were corrected, and the corrections do not say what everything else came to.
         *
         * @param lit the probes a row was recorded at
         */
        public AsRun asRunWith(java.util.Set<Integer> lit) {
            Map<ControlPointId, Reachability> out = new LinkedHashMap<>(found);
            java.util.Set<Integer> provedWrong = new java.util.LinkedHashSet<>();
            found.forEach((where, said) -> {
                if (!(where instanceof ControlPointId.ArmOccurrence arm)
                        || arm.probe().isEmpty() || !lit.contains(arm.probe().getAsInt())) {
                    return;
                }
                if (said instanceof Reachability.Unreachable) {
                    provedWrong.add(arm.probe().getAsInt());
                }
                out.put(where, new Reachability.Reachable(
                        new Witness.ARunWentThrough(arm.probe().getAsInt())));
            });
            return new AsRun(new Answers(out), provedWrong);
        }

        /**
         * What arrives once the rows have run, and where this reading was shown wrong.
         *
         * @param provedWrong arms proven unreachable that a row went through anyway. Nothing about
         *                    the model is wrong then — this reading is — and a measure says so
         *                    rather than quietly counting the arm again
         */
        public record AsRun(Answers answers, java.util.Set<Integer> provedWrong) {

            public AsRun {
                provedWrong = java.util.Set.copyOf(provedWrong);
            }
        }

        /** Whether this reading proved nothing arrives anywhere, which is what a walk that would
         *  only ever answer "keep everything" can skip on. */
        public boolean provesNothingUnreached() {
            return found.values().stream().noneMatch(Reachability.Unreachable.class::isInstance);
        }

        /** Whether nothing arrives at the arm recorded at {@code probe}. What every denominator
         *  takes an arm out by, and the one arm of the answer that takes anything out. */
        public boolean nothingArrivesAt(int probe) {
            for (Map.Entry<ControlPointId, Reachability> each : found.entrySet()) {
                if (each.getKey() instanceof ControlPointId.ArmOccurrence arm
                        && arm.probe().isPresent() && arm.probe().getAsInt() == probe) {
                    return each.getValue() instanceof Reachability.Unreachable;
                }
            }
            return false;
        }

        /** Whether the comparison at {@code probe} divides nothing that gets to it — one of its two
         *  outcomes being one nothing takes. */
        public boolean dividesNothing(int probe) {
            return atComparison(probe, true) instanceof Reachability.Unreachable
                    || atComparison(probe, false) instanceof Reachability.Unreachable;
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
                             CoverageSites.Plan plan, InputDomain read, Symbols symbols) {
        if (fn == null || spec == null) {
            return Answers.NONE;
        }
        Scope params = Scope.NONE;
        for (int i = 0; i < spec.params().size() && i < fn.params().size(); i++) {
            params = params.with(fn.params().get(i).binder(),
                    TypeOps.successType(spec.params().get(i).type()));
        }
        return of(body, params, plan, read, symbols);
    }

    /**
     * The same, told the bindings outright.
     *
     * <p>Fail-open throughout. A condition of a shape the rules have no word for narrows nothing,
     * so the arms under it come out unsettled rather than proven either way; a walk that falls over
     * answers about what it had reached and no more.
     */
    public static Answers of(Core body, Scope params, CoverageSites.Plan plan, InputDomain read,
                             Symbols symbols) {
        if (body == null || plan.isEmpty()) {
            return Answers.NONE;
        }
        PathEngine engine = new PathEngine(symbols, Map.of(), Terms.Of.THE_TREE_THAT_RUNS);
        Map<ControlPointId, Reachability> out = new LinkedHashMap<>();
        try {
            PathEngine.Entered in = PathEngine.Entered.nothing();
            for (Map.Entry<BindingId, Scope.Binding> p : params.bindings().entrySet()) {
                in = engine.enter(new Core.Read(p.getValue().name(), p.getKey(),
                        p.getValue().type(), body.pos()), in.known(), in.at());
            }
            new PathReachability(engine, plan, read == null ? InputDomain.NONE : read, symbols, out)
                    .walk(body, in.known(), in.at(),
                            InputReads.of(read == null ? InputDomain.NONE : read), List.of(), true);
        } catch (RuntimeException why) {
            // The run-time check is the backstop for the analysis this borrows, and it is the
            // backstop for this too: what was not read leaves an obligation standing.
            InvariantChecker.gaveUp("reachability", why);
        }
        return new Answers(out);
    }

    private final PathEngine engine;
    private final CoverageSites.Plan plan;
    /** What the declarations leave each position, which is what a {@code match} arm is held
     *  against. A condition narrows a path; a case is refused or left by the rules themselves. */
    private final InputDomain read;
    private final Symbols symbols;
    private final Map<ControlPointId, Reachability> out;

    private PathReachability(PathEngine engine, CoverageSites.Plan plan, InputDomain read,
                             Symbols symbols, Map<ControlPointId, Reachability> out) {
        this.engine = engine;
        this.plan = plan;
        this.read = read;
        this.symbols = symbols;
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
    private void walk(Core e, Known k, Denotations at, InputReads reads,
                      List<PathDecision> decided, boolean nothingAbove) {
        if (e == null || k.reachesNothing()) {
            // Nothing stands here, so nothing below is a place anything arrives at either. The arm
            // that made it so was answered where it was entered; the arms under it are left absent,
            // which reads as unsettled — the outermost one is the place to say it, and saying it
            // again at every fork inside would be the same finding several times over.
            return;
        }
        switch (e) {
            case Core.If iff -> {
                walk(iff.cond(), k, at, reads, decided, nothingAbove);
                outcomes(iff.cond(), k, at, decided);
                ControlPointId.ArmOccurrence[] arms = plan.armsOf(iff);
                enterArm(arms, 0, iff, iff.then(), k, at, reads, decided, true);
                enterArm(arms, 1, iff, iff.els(), k, at, reads, decided, false);
            }
            case Core.LetIn li -> {
                walk(li.value(), k, at, reads, decided, nothingAbove);
                PathEngine.Entered in = engine.bindLet(li, k, at);
                // Inside what the `let` binds, so an arm of an expanded helper is read against the
                // position the call handed it. A binding is not a fork, so what stands above the
                // body is what stood above the binding.
                walk(li.body(), in.known(), in.at(), reads.and(li.binder(), li.value()), decided,
                        nothingAbove);
            }
            case Core.Match match -> {
                walk(match.scrutinee(), k, at, reads, decided, nothingAbove);
                cases(match, reads, nothingAbove);
                // The scrutinee once and then the arms, written out rather than left to the generic
                // walk. A `Match`'s children are its scrutinee as well as its arm bodies, so
                // walking them all reads the scrutinee a second time — under a fork this time,
                // which takes back what was answered about anything in it.
                //
                // Each arm binds a value of the case it matched, which is a location holding
                // whatever that type guarantees: an arm of `| Paid p ->` reads `p`'s invariant, and
                // a guard inside it settles against that. Entering it is how the arm gets it, the
                // same act a parameter gets it by.
                //
                // Under an arm, this fork stands above whatever is inside it. Which arm was taken
                // is not recorded as a decision: nothing was assumed from it, and a proof naming it
                // would claim work the domains did not do.
                for (Core.Case arm : match.cases()) {
                    PathEngine.Entered in = engine.enter(
                            Terms.read(arm.binding(), arm.bindType(), arm.pos()), k, at);
                    walk(arm.body(), in.known(), in.at(), reads, decided, false);
                }
            }
            default -> {
                Core.forEachChild(e, child -> walk(child, k, at, reads, decided, nothingAbove));
            }
        }
    }

    /**
     * Each comparison of a condition, read under what holds where that comparison runs.
     *
     * <p>Not under what holds at the fork. A condition stops as soon as it is settled, so the
     * right-hand side of an {@code &&} runs only where the left-hand side held and the right-hand
     * side of an {@code ||} only where it did not — and a comparison read under the fork's own
     * state would be read under conditions that were never established when it ran.
     *
     * <p>Descends through {@code &&} and {@code ||} only, which is what a condition is built out of
     * and what the plan numbered. Anything else is a leaf: the plan answers for it or does not, and
     * a node it numbered nothing at is one nothing is filed about.
     */
    private void outcomes(Core cond, Known k, Denotations at, List<PathDecision> decided) {
        if (cond instanceof Core.Binary b
                && (b.op() == Hir.BinOp.AND || b.op() == Hir.BinOp.OR)) {
            outcomes(b.left(), k, at, decided);
            // The side that reaches the right operand: `&&` gets there having held, `||` having
            // failed. Read the other way round, a comparison guarded by its neighbour would be
            // proven against conditions nothing on the way to it established.
            boolean reachedWhen = b.op() == Hir.BinOp.AND;
            outcomes(b.right(), engine.assuming(b.left(), k, at, reachedWhen).known(), at,
                    with(decided, b.left().pos(), reachedWhen));
            return;
        }
        for (boolean result : new boolean[] {true, false}) {
            var where = plan.outcomeOf(cond, result);
            if (where.isEmpty()) {
                continue;
            }
            Predicates.Assumed taken = engine.assuming(cond, k, at, result);
            out.put(where.get(), taken.known().reachesNothing()
                    ? new Reachability.Unreachable(new Proof.ConflictingPathConditions(
                            with(decided, cond.pos(), result)))
                    : Reachability.notSettled(whyNot(taken, cond)));
        }
    }

    /**
     * Why an arm this could not prove is left as it was.
     *
     * <p>Two ways of settling nothing, and they are owed different things. A condition of a shape
     * no rule here reads is this compiler's limit, and widening the reading removes it; a condition
     * read to no effect is the ordinary state of a branch nobody built a value for, and no widening
     * touches it. Told apart by asking the reading, not by comparing the state it answered with to
     * the state it was given — that comparison says whether anything changed, which is neither.
     */
    private static WhyUnsettled whyNot(Predicates.Assumed taken, Core cond) {
        return taken.read() ? new WhyUnsettled.NoWitness()
                : new WhyUnsettled.AConditionWasNotRead(cond.pos());
    }

    private static List<PathDecision> with(List<PathDecision> decided, SourcePos at, boolean held) {
        List<PathDecision> out = new ArrayList<>(decided);
        out.add(new PathDecision(at, held));
        return out;
    }

    /**
     * One arm of a fork, read under its own side of the condition.
     *
     * <p>The answer is filed at the arm and the walk goes on inside it. Where the condition leaves
     * nothing, the arm is proven and what is under it is not walked: everything there is unreachable
     * for the same reason, and one finding is what an author is owed.
     */
    private void enterArm(ControlPointId.ArmOccurrence[] arms, int index, Core.If iff, Core arm,
                          Known k, Denotations at, InputReads reads, List<PathDecision> decided,
                          boolean holds) {
        Predicates.Assumed taken = engine.assuming(iff.cond(), k, at, holds);
        Known inside = taken.known();
        List<PathDecision> under = with(decided, iff.cond().pos(), holds);
        if (arms != null && index < arms.length) {
            out.put(arms[index], inside.reachesNothing()
                    ? new Reachability.Unreachable(new Proof.ConflictingPathConditions(under))
                    : Reachability.notSettled(whyNot(taken, iff.cond())));
        }
        walk(arm, inside, at, reads, under, false);
    }

    /**
     * Every arm of a {@code match}, held against what the rules leave the position matched on.
     *
     * <p>A different question from a condition's, and answered from a different place. A condition
     * narrows the path to an arm; a case is one the rules of the position refuse or leave, which is
     * as true three arms deep as at the first fork — a refusal is unconditional.
     *
     * <p>The other direction is not. That the rules <em>leave</em> a case says a caller can supply
     * one, which says something about arriving here only where nothing stands above: a fork the
     * body reaches first is reached by the behavior being applied at all. So the witness takes both
     * — every rule of the position read and leaving the case, and nothing decided on the way — and
     * is built here where both are in hand rather than assembled by whoever asks.
     */
    private void cases(Core.Match match, InputReads reads, boolean nothingAbove) {
        ControlPointId.ArmOccurrence[] arms = plan.armsOf(match);
        if (arms == null) {
            return;
        }
        TermPath path = reads.pathOf(match.scrutinee(), symbols);
        if (path == null) {
            return;   // not a position of this input: nothing here has rules about it
        }
        Position at = reads.read().at(path);
        for (int i = 0; i < match.cases().size() && i < arms.length; i++) {
            // A position this reading never got to — deeper than it reads into what a parameter
            // holds — states no such distinction, which is the position's own answer and not this
            // walk's. Said in its words so that a claim below the depth is told what it is told
            // everywhere else.
            Reachability said = at == null
                    ? Reachability.notSettled(new WhyUnsettled.ThePositionDidNotSettleIt(
                            new souther.compiler.inputs.Unsettlement.NoSuchDistinction()))
                    : saidOf(at, path, match.cases().get(i), nothingAbove);
            if (said != null) {
                out.put(arms[i], said);
            }
        }
    }

    /** What the rules leave one arm, or null where the arm names no case — a binding of the whole
     *  value, which the rules of the position say nothing about. */
    private Reachability saidOf(Position at, TermPath path, Core.Case arm, boolean nothingAbove) {
        List<TypeSymbol> named = arm.caseTypes();
        if (named.isEmpty()) {
            return null;
        }
        if (named.stream().allMatch(each -> at.admissionOf(each) instanceof Admits.Refused)) {
            // Every case it is written for is one the rules refuse, so an arm a row could still
            // take is not among these: an arm goes only where all of them go.
            return new Reachability.Unreachable(new Proof.EveryCaseRefused(path.toString(), named));
        }
        for (TypeSymbol each : named) {
            if (at.admissionOf(each) instanceof Admits.Unsettled unsettled) {
                return Reachability.notSettled(
                        new WhyUnsettled.ThePositionDidNotSettleIt(unsettled.why()));
            }
        }
        // Every one of them left standing, so a caller can supply one. Whether it arrives at this
        // fork as well is the other half, and nothing standing above is the one answer that settles
        // it: a fork the body reaches first is reached by the behavior being applied at all.
        return nothingAbove
                ? new Reachability.Reachable(
                        new Witness.EveryRuleReadAndNothingAbove(path.toString()))
                : Reachability.notSettled(new WhyUnsettled.NoWitness());
    }
}
