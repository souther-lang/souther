package souther.compiler.examples;

import souther.compiler.generated.MemoryClassLoader;
import souther.compiler.check.BehaviorRequirement;
import souther.compiler.check.Symbols;
import souther.compiler.ast.Hir;
import souther.compiler.check.Sig;
import souther.compiler.check.BoundaryInput;
import souther.compiler.check.BoundaryOutput;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.check.TypeOps;
import souther.compiler.check.TypeView;
import souther.compiler.coverage.Probe;
import souther.compiler.diag.Diagnostic;
import souther.compiler.jvm.GeneratedClass;
import souther.compiler.jvm.SoutherJvmAbi;
import souther.compiler.diag.msg.ExampleMessage;
import souther.compiler.diag.DiagnosticRenderer;
import souther.compiler.evaluate.DepthLimitExceeded;
import souther.compiler.evaluate.EvaluationContext;
import souther.compiler.evaluate.StepLimitExceeded;
import souther.compiler.diag.SourcePos;
import souther.compiler.diag.SourceRef;
import souther.compiler.observe.Disposition;
import souther.compiler.observe.FailurePhase;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.ObservedValue;
import souther.compiler.observe.RowIdentity;
import souther.compiler.observe.Applied;
import souther.compiler.observe.Counting;
import souther.compiler.observe.Run;
import souther.compiler.observe.RowOutcome;
import souther.compiler.observe.Stage;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.Set;

/**
 * Evaluates a module's {@code example}s at compile time and reports any mismatch as a compile error.
 * It mirrors {@link Runner}: it decodes each row's input expressions into the target
 * behavior's parameter types through their derived decoders, has the behavior applied to them, and
 * compares the result against the expected arm (a bare type name) or value (a construction/literal).
 * A failing example fails the build, exactly as a construction whose constant argument breaks its
 * invariant does.
 *
 * <p>What applies the behavior is not here. It is given to the run ({@link Answering}), because every
 * part of applying one is a fact about the loader its classes come from: which class the behavior is,
 * what its constructor takes, and what a stand-in has to be to be taken by it. What is here is what a
 * row <em>means</em> — which value a fixture states, which row of a fake's table answers, what an
 * answer is compared against, what a failure is reported as — and none of that changes with the
 * answerer. A row's inputs cross as {@link Handed} and the answer comes back as whatever the answerer
 * applies, read by the one reading a run has.
 *
 * <p>A behavior with a {@code let} body and a {@code >->} composition are evaluable; an injected
 * target is refused ({@code E1902}) — you fake one, you do not example it.
 * A {@code depends on} dependency is satisfied by a fake supplied at the example: a
 * {@code with dep = value} on the row (a constant/value dependency) or a {@code fake dep | table}
 * declaration (an input-keyed function dependency). What the fake answers is read here; making it
 * something the behavior can be constructed with is the answerer's ({@link DependencyStandin}).
 * Inputs, expected values, and fake entries are fixtures — literals, newtype constructions, record
 * constructions, and helpers applied to those (ADR-0077).
 *
 * <p>Two things a row needs are not here, because they are not about what an example means:
 * {@link FixtureReader} reads what a fixture states as the value it states — through
 * {@link NeutralForm} for the form a decoder reads and {@link HelperInvoker} for a helper run as the
 * method its module emits — and {@link RowEvaluation} owns the state one row builds up while it is
 * evaluated.
 *
 * <p>What a module <em>wrote</em> is not here either. {@link ExampleStatements} reads a module's
 * written statements against each other and reports where two of them answer differently, which is a
 * different question for a different key and reads none of this class's state. The one thing they
 * share is a fake's table: it is built there ({@link ExampleStatements#standins}) and answers by its
 * own rule ({@link ExampleStatements.Standins#answering}), and the stand-in a row runs against asks
 * the same one — a second reading of one table is what <em>E1919</em> exists to catch.
 */
public final class ExampleVerifier {

    /**
     * Evaluates every example in {@code module}; returns one diagnostic per failing example row
     * (empty when all pass). Does not throw for a failed example — the caller aggregates. A fixture
     * of an imported type decodes against its declaring module's package, which its
     * {@link TypeSymbol} names (a cross-module example).
     *
     * <p>Classes this compile did not generate resolve under {@code parent} — where an example calls
     * into a module that was compiled by another project, that is the loader its classes come from.
     *
     * <p>{@code requirements} says what each behavior takes injected and in what order: the fakes a
     * row supplies are passed to the injecting constructor in that order, which is the same answer
     * the emitter built that constructor from.
     *
     * <p>{@code values} are the values a row may name beyond this module's own: the ones its imports
     * bring in, each already closed over the module that published it (ADR-0074).
     *
     * <p>{@code answering} says what will apply a behavior for each row. The loader is built here
     * because it is this run's — a row's fixtures are decoded and held to their invariants whether or
     * not there is anything to run them against — and it is handed to {@code answering}, which is what
     * makes an answerer applying this compile's own classes one that can only exist over them.
     */
    public static Observations check(souther.compiler.check.Prepared.ExampleExecution module,
                                     Symbols symbols, Map<String, Sig> sigs,
                                     Map<String, byte[]> classes,
                                     Map<String, List<BehaviorRequirement>> requirements,
                                     ClassLoader parent, Map<String, Hir.FnDef> values,
                                     String sourceId, Deadline deadline, EvaluationPolicy policy,
                                     Answering answering) {
        if (module.examples().isEmpty()) {
            return Observations.NONE;
        }
        MemoryClassLoader loader = new MemoryClassLoader(classes, parent);
        ExampleVerifier v = new ExampleVerifier(module, symbols, sigs, requirements, loader, values,
                deadline, policy, answering.over(module.name(), loader));
        v.sourceId = sourceId;
        List<Diagnostic> failures = new ArrayList<>();
        List<RowOutcome> rows = new ArrayList<>();
        List<Incompleteness> incompleteness = new ArrayList<>();
        for (souther.compiler.check.Prepared.Rows block : module.examples()) {
            Hir.Example ex = block.read();
            try {
                v.checkExample(ex, failures, rows);
            } catch (LinkageError _) {
                // The generated classes would not link, so nothing could be evaluated here. The
                // case this was written for is the runtime being off the classpath (it is
                // `provided`, like CTFE), where the build-time pass still checks this example — but
                // a `LinkageError` is also what a class that will not verify raises, so what is
                // recorded is that the linking failed and not which of its causes it was. Nothing
                // was observed, and a measure that read the empty result as "no row covers this"
                // would report a gap nobody left.
                incompleteness.add(Incompleteness.at(Incompleteness.Code.LINKAGE_FAILED,
                        Incompleteness.Scope.BEHAVIOR, ex.target(),
                        new SourceRef(sourceId, ex.pos())));
            }
        }
        // A row that could not be decided is read here rather than restated at each place it happens,
        // so what a measure sees and what stopped it can never disagree.
        for (RowOutcome outcome : rows) {
            if (outcome.disposition() == Disposition.INCOMPLETE) {
                incompleteness.add(new Incompleteness(Incompleteness.Code.ROW_UNDECIDED,
                        new souther.compiler.observe.Target.OfBehavior(outcome.target()),
                        java.util.Optional.of(outcome.at())));
            }
        }
        return new Observations(failures, rows, incompleteness);
    }

    /**
     * What evaluating a source's rows turned up: the diagnostics it reports, the observation each row
     * left, and what stopped it from observing.
     *
     * <p>Not named {@code Result} because {@code net.unit8.raoh.Result} is what a decoder answers with
     * here, and a nested type of that name would take the spelling away from it.
     */
    public record Observations(List<Diagnostic> failures, List<RowOutcome> rows,
                               List<Incompleteness> incompleteness) {

        public static final Observations NONE = new Observations(List.of(), List.of(), List.of());

        public Observations {
            failures = List.copyOf(failures);
            rows = List.copyOf(rows);
            incompleteness = List.copyOf(incompleteness);
        }
    }

    /** The one-line form for a set of failures gathered across modules: the count, then the first
     * one's reason, matching what a single module's aggregate says. */
    public static String legacySummary(List<Diagnostic> failures) {
        Diagnostic first = failures.get(0);
        return failures.size() == 1
                ? legacyOf(first)
                : failures.size() + " examples do not hold; " + legacyOf(first);
    }

    /** A one-line message for a failing example: the body {@code getMessage()} is built from on the
     * exception these are thrown in. No surface prints it — the CLI, the annotation processor and the LSP all
     * render the diagnostics, which this exception carries — so what reads it is a caller holding
     * the exception, and it takes no language for the same reason
     * {@link DiagnosticRenderer#legacyBody} does not. */
    private static String legacyOf(Diagnostic d) {
        if (d.diff() != null) {
            // JUnit order: the expected value (what the example asserts) first, then what the
            // behavior actually produced.
            return "example does not hold: expected " + d.diff().expectedType()
                    + " but was " + d.diff().actualType();
        }
        // A diff-less failure (an input fixture that could not be built, a missing fake, a
        // non-termination): render the diagnostic's own catalog message so the reason travels
        // through the annotation processor, rather than collapsing to a bare "example failed".
        return d.said() == null ? "example failed" : DiagnosticRenderer.legacyBody(d);
    }

    private final souther.compiler.check.Prepared.ExampleExecution module;
    private final Symbols symbols;
    private final Map<String, Sig> sigs;
    /** What each behavior of this module takes injected, in the order its constructor takes it. */
    private final Map<String, List<BehaviorRequirement>> requirements;
    private final MemoryClassLoader loader;
    /** The values a row may name: this module's own, and the ones its imports bring in. */
    private final Map<String, Hir.FnDef> values;
    /** Which source the rows being evaluated are written in. A module's rows come from its own source
     * and from any number of attached {@code examples for} files, and a position alone stops saying
     * which once they are gathered under the module's name. */
    private String sourceId;
    /** What one row gets to be evaluated within ({@link #checkRow}). Carried rather than looked up,
     * so two compiles in one JVM need not agree on it. Reading a written statement is held to a
     * deadline of its own, which is {@link ExampleStatements}'. */
    private final Deadline deadline;
    /** What one row's evaluation is allowed: the steps and the depth it is decided by, and the wait
     * the machinery running it is given. */
    private final EvaluationPolicy policy;
    /** What applies a behavior for a row. One for the run, so no row's meaning depends on which
     * answerer it had. */
    private final Answerer answerer;

    private ExampleVerifier(souther.compiler.check.Prepared.ExampleExecution module,
                            Symbols symbols, Map<String, Sig> sigs,
                            Map<String, List<BehaviorRequirement>> requirements,
                            MemoryClassLoader loader, Map<String, Hir.FnDef> values,
                            Deadline deadline, EvaluationPolicy policy, Answerer answerer) {
        this.module = module;
        this.symbols = symbols;
        this.sigs = sigs;
        this.requirements = requirements;
        this.loader = loader;
        this.values = values;
        this.deadline = deadline;
        this.policy = policy;
        this.answerer = answerer;
    }

    /**
     * A reader for one row, held for as long as evaluating that row lasts.
     *
     * <p>Never shared between two of them. What a reading builds up — the bindings in force, the
     * values being expanded, the helper it is inside — is that row's, and a worker that ran out of
     * its budget goes on writing to it after the answer was given up on. So the isolation is the
     * reader, and it is the reader alone: everything else this class holds is read-only once a row
     * starts.
     */
    private FixtureReader newFixtureReader() {
        return new FixtureReader(module, symbols, values, loader);
    }

    // --- one example (a target and its rows) --------------------------------------------------

    private void checkExample(Hir.Example ex, List<Diagnostic> out, List<RowOutcome> rows) {
        ExampleTarget target = targetOf(ex.target());
        if (target == null) {
            out.add(notRunnable(ex));
            return;
        }
        Sig sig = sigs.get(target.name());
        if (sig == null) {
            throw new IllegalStateException("`" + target.name() + "` is evaluable but has no signature");
        }
        Set<TypeSymbol> outCases = outCases(sig.outputType());
        for (Hir.ExampleRow row : ex.rows()) {
            checkRow(target, sig, outCases, row, out, rows);
        }
    }

    /**
     * What a row runs: the behavior's name, and what it takes injected in the order its constructor
     * takes it.
     *
     * <p>Which kind of behavior it is does not survive to here. A row applies the class the module
     * emitted, and that class is reached the same way whichever way the behavior was written — the
     * name says which, and the requirements say what to hand it.
     */
    private record ExampleTarget(String name, List<BehaviorRequirement> requirements,
                                 boolean pending) {}

    /**
     * The behavior a row is about, and whether there is anything to run it against.
     *
     * <p>A behavior with a {@code let} body and a {@code >->} composition are applied; an injected one
     * has no body yet, so its rows are <em>recorded</em> rather than evaluated (spec
     * {@code example-pending}). That is not a lesser state: a model being migrated onto is injected
     * everywhere at the start, and the rows harvested from the system it replaces are what says what
     * each behavior owes. They are checked as far as they can be — every fixture is built, so a value
     * that breaks an invariant is found the day it is written — and evaluation begins by itself the
     * moment a {@code let} arrives.
     *
     * <p>Null when this module declares no behavior of that name; what to say about that is
     * {@link #notRunnable}'s.
     *
     * <p>A composition is run by applying the class its module emits, the same class normal execution
     * applies. Its stages with a body are constructed by it and handed the fields they need, so what
     * a row has to supply are the injected behaviors the stages reach — which is what its requirement
     * list holds, in the order its constructor takes them.
     */
    private ExampleTarget targetOf(String name) {
        for (Hir.BehaviorDef b : module.behaviors()) {
            if (!b.name().equals(name)) {
                continue;
            }
            return new ExampleTarget(name, requirements.getOrDefault(name, List.of()),
                    isPending(module.behaviors(), defined(), name));
        }
        return null;
    }

    /**
     * Whether a behavior of {@code module} has no implementation to run — an injected one (spec
     * {@code injected-behavior}).
     *
     * <p>Asked here by the row evaluation and by the adequacy report, which decides what it can measure
     * from the same answer. Two statements of it would let a report say a behavior is implemented while
     * its rows are being recorded rather than run.
     */
    public static boolean isPending(List<Hir.BehaviorDef> behaviors, Collection<String> defined,
                                    String name) {
        for (Hir.BehaviorDef b : behaviors) {
            if (b.name().equals(name)) {
                return b instanceof Hir.SpecBehavior && !defined.contains(name);
            }
        }
        return false;
    }

    /** The names the module's definitions are written under. What this asks of them is that there
     * is one, so it is handed the names and not the definitions: a reader taking the desugared
     * definitions would be asking for a claim it has no use for. */
    public static Set<String> definedNames(List<souther.compiler.check.Desugared.Fn> fns) {
        Set<String> names = new LinkedHashSet<>();
        for (souther.compiler.check.Desugared.Fn fn : fns) {
            names.add(fn.name());
        }
        return names;
    }

    private Collection<String> defined() {
        return definedNames(module.fns());
    }

    private boolean hasFn(String name) {
        return defined().contains(name);
    }

    /** The injected behavior named {@code name} in this module (a SpecBehavior with no {@code let}),
     * i.e. a valid target for a fake; null if not found or not injected. */
    private Hir.SpecBehavior injectedSpec(String name) {
        for (Hir.BehaviorDef b : module.behaviors()) {
            if (b instanceof Hir.SpecBehavior spec && spec.name().equals(name) && !hasFn(name)) {
                return spec;
            }
        }
        return null;
    }

    /**
     * The diagnostic for a target this module declares no behavior for: a name it does not know
     * ({@code E1901}), or a helper {@code let} of that name ({@code E1902}).
     *
     * <p>Only reached when {@link #targetOf} found no behavior, so being injected is not one of the
     * reasons any more: an injected behavior is a behavior, and its rows are recorded. What is left
     * for {@code E1902} is a target that is not a behavior at all.
     */
    private Diagnostic notRunnable(Hir.Example ex) {
        String name = ex.target();
        boolean isHelper = module.fns().stream().anyMatch(f -> f.name().equals(name));
        if (!isHelper) {
            return Diagnostic.at(ex.pos()).say(new ExampleMessage.NoBehaviorOfThatName(name)).build();
        }
        return Diagnostic.at(ex.pos())
                .say(new ExampleMessage.TheTargetCannotBeEvaluated(name))
                .hint(new ExampleMessage.WhatAnExampleRuns(
                        "it is a helper `let`, and this module declares no behavior of that name"))
                .build();
    }

    // --- one row ------------------------------------------------------------------------------

    /**
     * One row's evaluation, and the state it builds up while it runs: its own diagnostics, and the
     * helper it is currently inside.
     *
     * <p>A row that does not finish leaves its worker running — a pure computation reaches no interrupt
     * point, so cancelling it is a request and not a stop. So nothing that worker can still write to is
     * read by the rows after it: the evaluation has its own {@link FixtureReader}, so the state a
     * fixture builds up (which values it is expanding, which helper it is in) belongs to this row, and
     * the diagnostics it produces are its own list, handed to the caller only when it finishes. A late
     * result is dropped rather than landing among another row's.
     *
     * <p>One reader for the whole row, and that is what makes the reader the right thing to isolate.
     * The inputs, the expectation, each {@code with} and every fake table the row resolves are read
     * through this one — so a row that does not finish inside a fake table's helper is still a row
     * inside a helper, and the budget can name it ({@link #helper()}). Two readers would have put that
     * answer where nothing reporting the timeout could see it.
     */
    private static final class RowEvaluation implements java.util.concurrent.Callable<List<Diagnostic>> {

        private final ExampleVerifier verifier;
        /** This row's, and only this row's. */
        private final FixtureReader fixtures;
        private final ExampleTarget target;
        private final Sig sig;
        private final Set<TypeSymbol> outCases;
        private final Hir.ExampleRow row;
        private final RowState state = new RowState();

        RowEvaluation(ExampleVerifier of, ExampleTarget target, Sig sig,
                      Set<TypeSymbol> outCases, Hir.ExampleRow row) {
            this.verifier = of;
            this.fixtures = of.newFixtureReader();
            this.target = target;
            this.sig = sig;
            this.outCases = outCases;
            this.row = row;
        }

        /**
         * The row, and the arms it went through on the way.
         *
         * <p>The collecting is started and stopped here because a row is a thread: this worker runs
         * this row's body and nothing else, so what the probe saw on it is what this row reached. A row
         * that does not finish never gets here to read it, and the set goes with the thread's state —
         * which is what stops the next row on a reused worker from starting where this one left off.
         */
        @Override
        public List<Diagnostic> call() {
            List<Diagnostic> mine = new ArrayList<>();
            Probe.begin();
            // On this thread, because this thread is the evaluation: the budget belongs to the row,
            // and a worker reused for the next row would otherwise start where this one left off.
            EvaluationContext.begin(verifier.policy.stepLimit(),
                    verifier.policy.recursionDepthLimit());
            try {
                verifier.checkRowNow(fixtures, target, sig, outCases, row, mine, state);
                state.hits = Probe.taken();
            } finally {
                // Read on every way out, not only the one where the row came back. A row stopped by
                // its budget is the row whose cost is most worth knowing, and reading it after the
                // call that throws recorded nothing for exactly that row — which then said it had
                // spent nothing, the same thing a row that never ran says.
                state.stepsSpent = EvaluationContext.spent(verifier.policy.stepLimit());
                EvaluationContext.end();
                Probe.end();
            }
            return mine;
        }

        /** The helper this row is inside, for the budget to name when the row does not finish. */
        String helper() {
            return fixtures.runningHelper();
        }
    }

    /**
     * What a row's evaluation reached and saw.
     *
     * <p>{@link #stage} is written by the row's worker and read by the caller when the row runs out of
     * time — the one field read across that boundary, so it is the one field that is volatile. Whether
     * the row stopped in a fixture's helper or inside the behavior is exactly that difference, and a
     * timeout that cannot say which reports the same thing for two different problems.
     *
     * <p>Everything else is written by the worker and read only after it has finished, which the future
     * establishes: a row that does not finish has its state dropped rather than read.
     */
    private static final class RowState {
        private volatile Stage stage = Stage.NONE;
        /**
         * What applied the behavior, as whatever applied it said. Null until the row entered one.
         *
         * <p>Volatile for the same reason {@link #stage} is, and written before it: a row given up on
         * has both read from the other thread, and reading a stage that says the behavior was entered
         * has to mean the answer to what entered it is there to read.
         */
        private volatile Applied applied;
        private Disposition disposition = Disposition.FAILED;
        private FailurePhase failurePhase = FailurePhase.NONE;
        private TypeSymbol expectedArm;
        private TypeSymbol resultArm;
        private final List<TypeSymbol> inputCases = new ArrayList<>();
        private final List<ObservedValue> inputs = new ArrayList<>();
        /** The arms this row went through, where the classes it ran were generated to say. Empty
         * otherwise, and empty for a row that did not finish — a set read from a row still running
         * would be some of the arms rather than the arms. */
        private Set<Integer> hits = Set.of();
        /** What the row cost, in the unit it is held to. Written by the worker when it finishes, so
         * read only for a row that did. */
        private long stepsSpent;

        /** Records where the row stopped, and that it did. */
        void failed(FailurePhase phase) {
            this.disposition = Disposition.FAILED;
            this.failurePhase = phase;
        }

        /** Records that the row could not be decided — an absence of evidence, not a failure. */
        void incomplete(FailurePhase phase) {
            this.disposition = Disposition.INCOMPLETE;
            this.failurePhase = phase;
        }

        /**
         * How far the row had got and what had entered the behavior, read together.
         *
         * <p>One fact and one reading of it. Read as two, a row given up on can have its stage taken
         * before the worker moved and what applied it taken after, and the pair recorded is then a
         * row that never happened. The stage is read first, which is what makes the answer beside it
         * visible: both are volatile and the one that says a behavior was entered is written last.
         */
        Reached reached() {
            Stage at = stage;
            return new Reached(at, at.reached(Stage.INVOKED) ? applied : null);
        }
    }

    /** How far a row's evaluation got, and what had entered the behavior if anything had. */
    private record Reached(Stage stage, Applied applied) {}

    /** What the row turned out to be, from the state its worker left. */
    private RowOutcome outcomeOf(ExampleTarget target, Hir.ExampleRow row, RowState state) {
        Reached reached = state.reached();
        return new RowOutcome(new SourceRef(sourceId, row.pos()), target.name(), row.identity(),
                reached.stage(), state.disposition, state.failurePhase, state.expectedArm,
                state.resultArm, state.inputCases, state.inputs,
                ran(reached, new Counting.Read(state.stepsSpent, state.hits)));
    }

    /**
     * What became of the row's evaluation: what applied the behavior, and what this compile counted.
     *
     * <p>The first is what the row entered said of itself, taken where the row entered anything. Read
     * off the stage rather than restated, so a row that never entered a behavior cannot record
     * something as having applied it — and asked of what was entered rather than of the answerer,
     * because which of several things applies a behavior is settled per behavior. The second is taken
     * whatever the row reached, because the counting starts with the evaluation and a fixture applies
     * the helpers it names before the behavior is reached.
     */
    private static Run ran(Reached reached, Counting counting) {
        return new Run(reached.applied() == null ? new Applied.Nothing() : reached.applied(),
                counting);
    }

    /**
     * One row, evaluated within the budget: building its fixtures, running the helpers they apply,
     * applying the behavior and comparing the result are one evaluation, so a row cannot buy more time
     * by applying more helpers (ADR-0077). Only this thread adds to {@code out} — see
     * {@link RowEvaluation} for why the row's own worker must not.
     */
    private void checkRow(ExampleTarget target, Sig sig, Set<TypeSymbol> outCases, Hir.ExampleRow row,
                          List<Diagnostic> out, List<RowOutcome> rows) {
        RowEvaluation evaluation = new RowEvaluation(this, target, sig, outCases, row);
        switch (deadline.given(
                new Deadline.Work.Row(target.name(), sourceId, row.pos(), row.identity()),
                evaluation)) {
            case Deadline.Outcome.Finished(List<Diagnostic> found) -> {
                out.addAll(found);
                rows.add(outcomeOf(target, row, evaluation.state));
            }
            case Deadline.Outcome.Overran(Runnable abandon) -> {
                // Read what the row was doing before abandoning it: giving up interrupts the worker,
                // which may let it leave the helper it is in, and then the reason would depend on
                // which thread got there first.
                String helper = evaluation.helper();
                // Only what the worker publishes: the rest of its state is still being written. How
                // far it got is the difference between a fixture's helper that will not stop and a
                // behavior that will not stop, which is what the author has to know, and what entered
                // the behavior comes with it because the two are one reading.
                Reached reached = evaluation.state.reached();
                abandon.run();
                // Not E1910. What did not come back was not shown to go round more than an example
                // may — it was not counted at all, which is what an evaluation reaching code this
                // compile did not generate looks like. Saying the model does not terminate here would
                // put a diagnostic on a model that may be right, and send its author to make
                // something structural that already is.
                out.add(Diagnostic.at(row.pos())
                        .say(helper == null
                                ? new ExampleMessage.TheEvaluationDidNotAnswer(
                                        Long.toString(deadline.budgetMs()))
                                : new ExampleMessage.TheEvaluationDidNotAnswerWhileCalling(
                                        Long.toString(deadline.budgetMs()), helper))
                        .hint(new ExampleMessage.NotAnsweringIsNotNotTerminating()).build());
                // No spend is read: the worker is still writing to its state, and a count taken
                // while it runs would be some of what it spent rather than what it spent. That is
                // what the row says — not zero, which is what a row that passed no counted point
                // says.
                rows.add(new RowOutcome(new SourceRef(sourceId, row.pos()), target.name(),
                        row.identity(), reached.stage(), Disposition.INCOMPLETE,
                        FailurePhase.TIMEOUT, null, null, List.of(), List.of(),
                        ran(reached, new Counting.Unread())));
            }
            case Deadline.Outcome.Threw(Throwable cause) -> {
                // The evaluated code stopped itself, having gone through more than it was allowed.
                // What it spent is a property of what the row does, so this is the same answer on
                // every machine — which is the whole reason the code counts rather than the compiler
                // timing it.
                FailurePhase overspent = overspending(cause);
                if (overspent != null) {
                    out.add(overBudget(row, overspent));
                    evaluation.state.incomplete(overspent);
                    rows.add(outcomeOf(target, row, evaluation.state));
                    return;
                }
                // Every way the stack can run out arrives here, because everything the worker threw
                // arrives here. A site that happens to cross a reflection boundary names the helper
                // it was in; one that does not — a generated decoder, an encoder, the reader's own
                // walk — says only that it ran out, and both are the same answer about the same
                // thing. Classifying at the sites instead left the ones with no boundary to cross
                // falling through as a compiler failure.
                if (cause instanceof StackExhaustedException nt) {
                    out.add(stackRanOut(row, nt.getMessage()));
                    evaluation.state.incomplete(FailurePhase.STACK_EXHAUSTED);
                    rows.add(outcomeOf(target, row, evaluation.state));
                    return;
                }
                if (cause instanceof StackOverflowError) {
                    String helper = evaluation.helper();
                    out.add(stackRanOut(row, helper == null ? "the evaluation overflowed the stack"
                            : "`" + helper + "` overflowed the stack"));
                    evaluation.state.incomplete(FailurePhase.STACK_EXHAUSTED);
                    rows.add(outcomeOf(target, row, evaluation.state));
                    return;
                }
                // Whoever is compiling asked to stop. Nothing is known about this row — no result was
                // produced and no comparison was made — so this is not a failing example, and
                // reporting it as one would put a diagnostic on a model that may be correct.
                if (cause instanceof java.util.concurrent.CancellationException) {
                    throw new java.util.concurrent.CancellationException(
                            "interrupted while evaluating an example of `" + target.name() + "`");
                }
                if (cause instanceof RuntimeException re) {
                    throw re;
                }
                throw new IllegalStateException(cause);
            }
        }
    }

    /**
     * Which budget {@code cause} says was spent, or null where it says nothing about a budget.
     *
     * <p>Told apart here rather than at each place code runs, because what an author does about the
     * two is not the same: a loop that will not stop is bounded or made structural, and a recursion
     * that goes too deep is made to recurse on a part of its argument.
     */
    private static FailurePhase overspending(Throwable cause) {
        if (cause instanceof StepLimitExceeded) {
            return FailurePhase.STEP_LIMIT;
        }
        if (cause instanceof DepthLimitExceeded) {
            return FailurePhase.DEPTH_LIMIT;
        }
        return null;
    }

    /**
     * The evaluation went through more than the policy allows.
     *
     * <p>What this says is what the counting establishes and no more: the evaluation did not finish
     * within the budget. Whether the model terminates is a different question and this cannot answer
     * it — a `partial` recursion that never stops reaches this, and so does one that would have
     * stopped a hundred steps later. Reported as "this example did not terminate", it told the author
     * of a model that does terminate that their model does not, and pointed them at a recursion to
     * make structural that already was.
     *
     * <p>The two budgets are said apart because what to do about them differs: a loop is bounded or
     * given more, and a recursion is made structural or given more depth. Each names the limit it
     * reached and the setting that sets it, so the reader can tell which of the two answers applies
     * to them without being told which one their model is.
     */
    private Diagnostic overBudget(Hir.ExampleRow row, FailurePhase which) {
        boolean depth = which == FailurePhase.DEPTH_LIMIT;
        return Diagnostic.at(row.pos())
                // As written, not as a number the locale groups: `50,000` is not a budget anyone
                // set, and the setting that sets it takes the ungrouped form.
                .say(depth
                        ? new ExampleMessage.TheEvaluationReachedItsDepthLimit(
                                Integer.toString(policy.recursionDepthLimit()))
                        : new ExampleMessage.TheEvaluationSpentItsSteps(
                                Long.toString(policy.stepLimit())))
                .hint(depth ? new ExampleMessage.ReachingTheDepthLimitIsNotDiverging()
                        : new ExampleMessage.SpendingTheBudgetIsNotDiverging())
                .build();
    }

    /**
     * The JVM stack ran out before the counted depth limit was reached.
     *
     * <p>Not E1910 either, and for a reason of its own: how many frames a stack holds is decided by
     * how large they are, which is the helper's business and the JIT's. The depth limit is what is
     * meant to stop a recursion, and reaching this instead means the two are set wrong for this model
     * — which the author can act on, and which says nothing about whether the recursion terminates.
     */
    private Diagnostic stackRanOut(Hir.ExampleRow row, String why) {
        return Diagnostic.at(row.pos())
                .say(new ExampleMessage.TheStackRanOutBeforeTheDepthLimit(why,
                        Integer.toString(policy.recursionDepthLimit())))
                .hint(new ExampleMessage.TheDepthLimitIsWhatShouldStopIt()).build();
    }

    private void checkRowNow(FixtureReader fixtures, ExampleTarget target, Sig sig,
                             Set<TypeSymbol> outCases, Hir.ExampleRow row, List<Diagnostic> out,
                             RowState state) {
        List<BoundaryInput> ins = sig.ins();
        if (row.inputs().size() != ins.size()) {
            out.add(Diagnostic.at(row.pos())
                    .say(new ExampleMessage.TheRowHandsOverAnotherNumberOfInputs(target.name(),
                            String.valueOf(ins.size()), String.valueOf(row.inputs().size())))
                    .build());
            state.failed(FailurePhase.INPUT_FIXTURE);
            return;
        }
        Object[] args = new Object[ins.size()];
        for (int i = 0; i < ins.size(); i++) {
            try {
                args[i] = fixtures.built(row.inputs().get(i), ins.get(i));
            } catch (FixtureException fe) {
                out.add(Diagnostic.at(row.pos())
                        .say(new ExampleMessage.AnInputCouldNotBeBuilt(target.name(),
                                String.valueOf(i + 1), fe.getMessage()))
                        .build());
                state.failed(FailurePhase.INPUT_FIXTURE);
                return;
            }
            state.inputCases.add(caseWritten(fixtures, row.inputs().get(i), ins.get(i).type()));
            state.inputs.add(fixtures.observed(args[i]));
        }
        // validate the expected arm/value against the output cases before running. Which case the row
        // asserts is read through what it names, so a row may name a value where it may name a case.
        // Only where that answers is there an arm to hold against the target's: a helper answers with a
        // case nothing here can read off the text, and reporting that as an arm the target cannot produce
        // refused a row whose expectation was right (issue #214).
        TypeSymbol named = fixtures.constructedCase(row.expected());
        state.expectedArm = named;
        if (named != null && !outCases.isEmpty() && !outCases.contains(named)) {
            String expectedArm = fixtures.expectedArm(row.expected());
            List<String> names = new ArrayList<>();
            for (TypeSymbol c : outCases) {
                names.add(c.name());
            }
            out.add(Diagnostic.at(row.pos())
                    .say(new ExampleMessage.NotOneOfTheResultCases(
                            expectedArm != null ? expectedArm : named.name(), target.name()))
                    .hint(new ExampleMessage.TheResultCasesAre(String.join(", ", names))).build());
            state.failed(FailurePhase.EXPECTED_FIXTURE);
            return;
        }
        // Build the expected value before running: a row whose expectation cannot be built states no
        // expectation, and comparing a result against a value nothing built reported a mismatch
        // against an empty expected value — a wrong answer for a row that was right.
        Asserted asserted;
        try {
            asserted = fixtures.caseOnly(row.expected()) != null ? null
                    : fixtures.assertedExpected(row.expected(), sig.out());
        } catch (FixtureException fe) {
            out.add(Diagnostic.at(row.pos())
                    .say(new ExampleMessage.TheExpectedValueCouldNotBeBuilt(target.name(),
                            fe.getMessage()))
                    .build());
            state.failed(FailurePhase.EXPECTED_FIXTURE);
            return;
        }
        state.stage = Stage.FIXTURES_VALIDATED;
        if (target.pending()) {
            // Everything a row can be held to without a body has been: its arity, its inputs against
            // their types and invariants, and its expectation against the output's cases. What is left
            // needs something to run, and there is nothing yet. A fake is not it — a fake stands in for
            // a dependency while some *other* behavior's row runs, and this row is about this behavior.
            state.disposition = Disposition.PENDING;
            state.failurePhase = FailurePhase.NONE;
            return;
        }
        List<DependencyStandin> standins = resolveFakes(fixtures, target, row, out);
        if (standins == null) {
            state.failed(FailurePhase.FAKE_RESOLUTION);
            return;   // a fake was missing/invalid; the diagnostic is already reported
        }
        Answerer.Applying applying;
        try {
            applying = answerer.applying(target.name(), standins);
        } catch (StandinNotBuilt e) {
            // The row states the stand-in and it could not be made into an instance the behavior can
            // be constructed with. Nothing was applied, so the row stops where a row whose dependency
            // has no fake stops, and says the same thing about itself.
            out.add(ExampleStatements.unbuildableFake(whereDeclared(e.dependency(), row),
                    e.dependency(), e.getMessage()));
            state.failed(FailurePhase.FAKE_RESOLUTION);
            return;
        }
        Object result;
        // What entered it before that it entered, so a row given up on cannot be read as having
        // entered a behavior with nothing saying what did.
        state.applied = applying.applied();
        state.stage = Stage.INVOKED;
        try {
            result = applying.to(handed(fixtures, target, args, ins));
        } catch (InvocationFailure f) {
            applicationFailed(fixtures, row, asserted, f.getCause(), out, state);
            return;
        } catch (ImplementationNotReached e) {
            // Nothing was applied: what would have applied it could not be reached. Told as the row
            // aborting, which is what it was told while this and the applied code failing arrived as
            // one throw — saying it differently is a change to what a row is told, and a different
            // thing from where the two are told apart.
            neverEntered(state);
            aborted(fixtures, row, asserted, String.valueOf(e.getMessage()), out, state);
            return;
        } catch (FixtureException fe) {
            // The row's input could not be put in the form the answerer reads. Nothing about the row
            // was established — it was never handed over — so it is undecided rather than failed, and
            // no diagnostic is said about a model that may be right. Which is as far as this goes:
            // no answerer a compile has crosses, so what more to say about such a row is settled by
            // whatever first supplies one that does.
            neverEntered(state);
            state.incomplete(FailurePhase.INFRASTRUCTURE);
            return;
        }
        result = projected(result, sig.outputType());
        // The case the run answered with is the one the value is. Its class names the module that
        // declares it, and what this module means by that class's spelling is a different question.
        state.resultArm = fixtures.typeOf(result);
        state.stage = Stage.COMPARED;
        TypeSymbol arm = fixtures.caseOnly(row.expected());
        if (arm != null) {
            // A bare case name asserts the arm and nothing under it, so there is no value to compare.
            if (!arm.equals(state.resultArm)) {
                out.add(mismatch(fixtures, row, arm.name(), fixtures.describeActual(result), null));
                state.failed(FailurePhase.COMPARISON);
                return;
            }
        } else {
            ValueMatch.Mismatch differs = fixtures.disagreement(asserted, result, sig.outputType());
            if (differs != null) {
                // The whole of each side, so the two can be read against each other, and then where
                // they part: a row that wrote a name the answer does not wear differs at one position
                // by its type, which reading two whole values does not say on its own.
                out.add(mismatch(fixtures, row, fixtures.shown(asserted),
                        fixtures.shown(fixtures.structured(result), sig.outputType()), differs));
                state.failed(FailurePhase.COMPARISON);
                return;
            }
        }
        state.disposition = Disposition.HELD;
        state.failurePhase = FailurePhase.NONE;
    }

    /**
     * The case an input fixture supplies at {@code position}, or null where its text does not say. A
     * form this cannot read is not a reason to lose the row: the measure that reads it says it could
     * not classify.
     *
     * <p>Read at the position and not off the fixture alone. A position writing its values under a
     * name divides into what its base divides into, so what a row there supplies is the case under
     * that name — the same projection, in the direction that reads rather than the one that derives.
     */
    private TypeSymbol caseWritten(FixtureReader fixtures, Hir.Expr fixture, Type position) {
        try {
            return fixtures.caseUnder(TypeView.of(position, symbols).wrappers().stream()
                    .map(TypeOps.Layer::named).toList(), fixture);
        } catch (RuntimeException e) {
            if (overspending(e) != null) {
                throw e;   // the row's budget is gone; it is not a form that could not be read
            }
            return null;
        }
    }

    /**
     * The Souther value behind a behavior's answer. A member this module declared is the answer
     * itself; a primitive or an imported type reached the union through a bridge case (spec §jvm-anonymous-union),
     * and a row writes the value, not the bridge case — which is a name this source does not have.
     * The same projection a Souther caller does, done on the loaded classes.
     */
    private Object projected(Object result, Type out) {
        if (result == null || !(out instanceof Type.Union)) {
            return result;
        }
        for (TypeSymbol member : TypeOps.leafCases(out, symbols)) {
            if (!member.isPrimitive() && member.module().equals(module.name())) {
                continue;
            }
            if (SoutherJvmAbi.nameOf(new GeneratedClass.BridgeCase(module.name(), member)).is(result.getClass())) {
                try {
                    return result.getClass().getMethod("value").invoke(result);
                } catch (ReflectiveOperationException e) {
                    throw new IllegalStateException("a bridge case with no `value`: " + result.getClass(), e);
                }
            }
        }
        return result;
    }

    // --- fakes for what a behavior depends on ---------------------------------------------------

    /**
     * What stands in for each of the target's requirements, in the order its constructor takes them;
     * null (with a diagnostic reported) when one is missing or invalid.
     *
     * <p>What a stand-in answers and nothing more. Making it something the behavior can be constructed
     * with is a fact about the loader the implementation comes from, so it is the answerer's
     * ({@link Answerer#applying}) — and reading a row's fakes is the same reading whoever that is.
     */
    private List<DependencyStandin> resolveFakes(FixtureReader fixtures, ExampleTarget target,
                                                 Hir.ExampleRow row, List<Diagnostic> out) {
        List<BehaviorRequirement> reqs = target.requirements();
        List<DependencyStandin> standins = new ArrayList<>(reqs.size());
        for (BehaviorRequirement req : reqs) {
            DependencyStandin standin = resolveFake(fixtures, target.name(), req, row, out);
            if (standin == null) {
                return null;
            }
            standins.add(standin);
        }
        return standins;
    }

    private DependencyStandin resolveFake(FixtureReader fixtures, String target,
                                          BehaviorRequirement req, Hir.ExampleRow row,
                                          List<Diagnostic> out) {
        String depName = req.dependency();
        Hir.SpecBehavior dep = injectedSpec(depName);
        if (dep == null) {
            out.add(fakeMissingDiag(target, req, row, "`" + depName
                    + "` is not an injected behavior of this module"));
            return null;
        }
        Sig depSig = sigs.get(depName);
        if (depSig == null) {
            out.add(fakeMissingDiag(target, req, row, "`" + depName
                    + "` has no signature to build a stand-in against"));
            return null;
        }
        BoundaryOutput outType = depSig.out();
        // a value fake given inline on the row: `with dep = value`
        for (Hir.With w : row.withs()) {
            if (w.dep().equals(depName)) {
                try {
                    Object value = fixtures.buildFixture(w.value(), outType).value();
                    // a constant: it ignores its inputs
                    return new DependencyStandin(depName, dep.params().size(), _ -> value);
                } catch (FixtureException fe) {
                    // The row does supply a fake. What failed is building its value, which is a
                    // different problem from a dependency nothing stands in for.
                    out.add(Diagnostic.at(w.value().pos())
                            .say(new ExampleMessage.TheFakeValueCouldNotBeBuilt(depName,
                                    fe.getMessage()))
                            .build());
                    return null;
                }
            }
        }
        // a function fake given as a `fake dep | table` declaration
        for (souther.compiler.check.Prepared.FakeTable table : module.fakes()) {
            Hir.Fake fk = table.read();
            if (fk.target().equals(depName)) {
                return tableStandin(fixtures, fk, dep, depSig);
            }
        }
        out.add(fakeMissingDiag(target, req, row, "add `with " + depName
                + " = ...` on the row, or a `fake " + depName + "` table"));
        return null;
    }

    /**
     * A dependency nothing stands in for. Where the target is not the definition that asked for it —
     * a composition takes the requirements of its stages — the stage that wants it is named, so the
     * author is not left to walk the composition to find out which one.
     */
    private Diagnostic fakeMissingDiag(String target, BehaviorRequirement req, Hir.ExampleRow row,
                                       String detail) {
        List<String> stages = new ArrayList<>();
        for (String requester : req.requiredBy()) {
            if (!requester.equals(target)) {
                stages.add("`" + requester + "`");
            }
        }
        Diagnostic.Builder d = stages.isEmpty()
                ? Diagnostic.at(row.pos())
                        .say(new ExampleMessage.ADependencyHasNoFake(target, req.dependency()))
                : Diagnostic.at(row.pos())
                        .say(new ExampleMessage.ADependencyReachedThroughHasNoFake(target,
                                req.dependency(), String.join(", ", stages)));
        return d.hint(new ExampleMessage.WriteAFakeLikeThis(detail)).build();
    }

    /** Precomputes a function fake's input→output table (decoded fixtures) as a tuple-keyed lookup, and
     * answers by matching an actual input tuple by value equality, falling back to the {@code _}
     * default or a miss. Works for any arity: a 0/1-input dep's tuple has 0/1 elements, a 2+-input
     * dep's has one per parameter (issue #57). */
    private DependencyStandin tableStandin(FixtureReader fixtures, Hir.Fake fk, Hir.SpecBehavior dep,
                                           Sig depSig) {
        // The dependency's own signature, which admitted what its boundary carries. Rebuilding the
        // types from what it declared would put them through that walk a second time, and a
        // stand-in stands where the behavior does.
        List<BoundaryInput> paramTypes = depSig.ins();
        // Built the one way a table is built ({@link ExampleStatements#standins}), on this row's own
        // reader, so a row that does not finish inside a table's helper is still inside a helper. What
        // is wrong with the table is said where the fake is written, and said once: this row and every
        // other row reaching the same fake would each repeat the one thing wrong with the one table.
        ExampleStatements.BuiltTable built =
                ExampleStatements.standins(fixtures, fk, paramTypes, depSig.out(), new ArrayList<>());
        if (built == null) {
            return null;
        }
        // The dispatch, which is what a row runs against. What the table was written with and cannot
        // dispatch to is said where the fake is written, and is nothing a stand-in can answer with.
        ExampleStatements.Standins table = built.standins();
        String depName = fk.target();
        int arity = paramTypes.size();
        java.util.function.Function<Object[], Object> body = a -> {
            Object[] key = java.util.Arrays.copyOf(a, arity);
            // The table's own rule, which is the rule the reading that holds it against the rows
            // recorded for the behavior asks too. One answer to "which row answers this" (E1919).
            ExampleStatements.Standin answering = table.answering(key);
            if (answering == null) {
                throw new FakeMissException("`" + depName + "` has no output for "
                        + java.util.Arrays.toString(key));
            }
            return answering.answer().value();
        };
        return new DependencyStandin(depName, dep.params().size(), body);
    }

    /** Where the dependency a stand-in was written for is declared, for a report about the stand-in to
     * be quoted against. The row's own position where this module declares nothing of that name, which
     * cannot arise for a stand-in that was resolved and is not worth a second reading to rule out. */
    private SourcePos whereDeclared(String dependency, Hir.ExampleRow row) {
        Hir.SpecBehavior dep = injectedSpec(dependency);
        return dep == null ? row.pos() : dep.pos();
    }


    private Diagnostic mismatch(FixtureReader fixtures, Hir.ExampleRow row, String expected,
                                String actual, ValueMatch.Mismatch differs) {
        // Underline the expected result (the part the row asserts), not the whole row, so the marker
        // lands on something meaningful rather than a single column at the row's start.
        SourcePos pos = row.expected() != null ? row.expected().pos() : row.pos();
        int width = Math.max(1, expected.length());
        Diagnostic.Builder b = Diagnostic.at(pos, width)
                .say(new ExampleMessage.TheRowDoesNotHold())
                .diff(actual, expected);
        // Where the two are of different types, the values alone do not say so — a newtype and the
        // base it wraps are written the same way by an encoder, and were reported as a mismatch
        // between two identical renderings. So the position and the two names are said.
        if (differs != null && differs.reason() == ValueMatch.Reason.TYPE) {
            b.hint(new ExampleMessage.TheTwoAreOfDifferentTypes(differs.path(),
                    fixtures.typeShown(differs.asserted()),
                    fixtures.typeShown(differs.observed(), differs.position())));
        }
        // The row's own words, where it has any. An unnamed row's ordinal is not words about the
        // row, and the position the report is already anchored at says which row it is.
        if (row.identity() instanceof RowIdentity.Named named) {
            b.hint(new ExampleMessage.WhatTheRowSaid(named.name()));
        }
        return b.build();
    }

    private Set<TypeSymbol> outCases(Type out) {
        return TypeOps.outputCases(out, symbols);
    }

    // --- what a row hands over, and what it makes of a failure ---------------------------------

    /**
     * The row's inputs as what it hands over: each value as this compile built it, and the form a
     * derived decoder reads, for an answerer whose classes are not this compile's.
     *
     * <p>The second is worked out only if it is asked for. The answerer this compile has of its own
     * applies the classes these values already are, so nothing crosses and nothing is walked.
     */
    private static List<Handed> handed(FixtureReader fixtures, ExampleTarget target, Object[] args,
                                       List<BoundaryInput> ins) {
        List<Handed> over = new ArrayList<>(args.length);
        for (int i = 0; i < args.length; i++) {
            Object built = args[i];
            BoundaryInput at = ins.get(i);
            String what = "input " + (i + 1) + " of `" + target.name() + "`";
            over.add(new Handed(built, () -> fixtures.neutral(built, at, what)));
        }
        return over;
    }

    /**
     * Takes back the row having entered the behavior.
     *
     * <p>A row is marked as having entered before the answerer is asked, because that is the one
     * thing a reader of a row that never comes back needs and it can only be published beforehand.
     * Where the answerer comes back saying it never got in, that mark is wrong: everything at
     * {@link Stage#INVOKED} says what applied it ({@link Run#applied()}), and nothing applied this.
     *
     * <p>Safe to write here and nowhere else. The reader across the thread boundary is the one that
     * reads a row still running, and a row that reached this came back.
     */
    private static void neverEntered(RowState state) {
        state.stage = Stage.FIXTURES_VALIDATED;
        state.applied = null;
    }

    /**
     * What the row makes of a failure the applied code came back with.
     *
     * <p>The one reading of it, and it is here rather than where the behavior was applied because it
     * is about the row: which phase it stopped in, what the author is told, whether it is a failure at
     * all. Whoever applied the behavior carried the failure out and said nothing about it
     * ({@link InvocationFailure}), so the same throw from this compile's own classes and from an
     * implementation supplied from outside is read the same way — which is what stops a row's meaning
     * from depending on which answerer it had.
     *
     * <p>A budget spent is raised on rather than read: it is about the row's cost, which is held to
     * where the row is given its deadline, and read as anything else the reason is lost.
     */
    private void applicationFailed(FixtureReader fixtures, Hir.ExampleRow row, Asserted asserted,
                                   Throwable cause, List<Diagnostic> out, RowState state) {
        if (overspending(cause) != null) {
            throw (RuntimeException) cause;
        }
        if (cause instanceof FakeMissException fm) {
            out.add(Diagnostic.at(row.pos())
                    .say(new ExampleMessage.AFakeHadNoOutputForAnInput(fm.getMessage()))
                    .build());
            state.failed(FailurePhase.FAKE_RESOLUTION);
            return;
        }
        // a point the model declared could not arise: what the row found is not a wrong answer but a
        // premise that does not hold, so it is reported as that rather than as a mismatch. Matched by
        // name: the applied code runs under its own loader, and this only needs to know which abort it
        // was.
        if (cause != null && "souther.runtime.UnreachableReached".equals(cause.getClass().getName())) {
            out.add(Diagnostic.at(row.pos())
                    .say(new ExampleMessage.TheRowReachedAnUnreachablePoint(cause.getMessage()))
                    .hint(new ExampleMessage.EitherTheRowOrTheReasonIsWrong()).build());
            state.failed(FailurePhase.INVOCATION);
            return;
        }
        if (cause instanceof StackOverflowError) {
            // Named where the behavior was applied, and told apart from a fixture's helper running
            // out, which is named where that happened.
            out.add(stackRanOut(row, "the behavior overflowed the stack"));
            state.incomplete(FailurePhase.STACK_EXHAUSTED);
            return;
        }
        aborted(fixtures, row, asserted,
                cause == null ? "aborted" : String.valueOf(cause.getMessage()), out, state);
    }

    /** The behavior stopped itself while the row ran — an invariant it broke, or anything else it
     * ended with. Reported against what the row said it would answer, so the two can be read together. */
    private void aborted(FixtureReader fixtures, Hir.ExampleRow row, Asserted asserted, String why,
                         List<Diagnostic> out, RowState state) {
        TypeSymbol only = fixtures.caseOnly(row.expected());
        String stated = asserted != null ? fixtures.shown(asserted)
                : only == null ? null : only.name();
        out.add(mismatch(fixtures, row, stated == null ? "the expected value" : stated,
                "aborted: " + why, null));
        state.failed(FailurePhase.INVOCATION);
    }

    /** A fake table had no output for an input the behavior asked for (and no {@code _} default). */
    private static final class FakeMissException extends RuntimeException {
        FakeMissException(String message) {
            super(message);
        }
    }
}
