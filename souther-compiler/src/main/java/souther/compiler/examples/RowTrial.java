package souther.compiler.examples;

import souther.compiler.execute.EvaluationPolicy;
import souther.compiler.execute.RowTrials;
import souther.compiler.ast.Hir;
import souther.compiler.check.BoundaryInput;
import souther.compiler.check.DeclarationKinds;
import souther.compiler.check.FakeTables;
import souther.compiler.check.Prepared;
import souther.compiler.check.Sig;
import souther.compiler.check.SumCases;
import souther.compiler.check.Symbols;
import souther.compiler.core.Contract;
import souther.compiler.coverage.Intervention;
import souther.compiler.coverage.NumberingIdentity;
import souther.compiler.coverage.Probe;
import souther.compiler.coverage.RunRecord;
import souther.compiler.evaluate.DepthLimitExceeded;
import souther.compiler.evaluate.EvaluationContext;
import souther.compiler.evaluate.StepLimitExceeded;
import souther.compiler.generated.GeneratedImplementations;
import souther.compiler.generated.MemoryClassLoader;
import souther.compiler.generated.ProbeImage;
import souther.compiler.jvm.ClassFileImage;
import souther.compiler.observe.AnswerChange;
import souther.compiler.observe.AnswerObservation;
import souther.compiler.observe.FieldTypes;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;

/**
 * Running a row nobody has written yet, to see where it goes.
 *
 * <p>What a generator cannot do for itself and cannot be told. Which combination of a body's
 * decisions a composed row sits in is settled by running it: everything up to that point is a
 * reading of the body, and a reading is what may be wrong.
 *
 * <p>The same classes an evaluation runs against, reached the same way a written row reaches them —
 * the values are built through this module's own decoders and handed to the answerer this compile
 * emitted, and a dependency the module states a table for is answered by that table exactly as it is
 * for a row somebody wrote. What differs is that there is no row: no expectation to hold the answer
 * to. What a candidate stands them in with travels
 * with the candidate, because which answer a rule takes is part of what the candidate is; a
 * behavior whose implementation is out of reach still cannot be applied, which is said outright by
 * the layer that would have applied it and comes back as nothing having run — asked of that layer
 * rather than worked out here from what a behavior declares, there being one question and no reason
 * for two answers to it.
 *
 * <p>A run that aborts still went where it went. An invariant refusing the answer, a budget running
 * out, an {@code unreachable} being reached — each of them happens after the row has passed whatever
 * it passed, and what was recorded up to that point is what the row did. So the recording is read on
 * every way out and the failure itself is dropped: nothing here is judging the row, and a generator
 * has no expectation for it to have failed against.
 */
public final class RowTrial {


    /**
     * A way to run rows against one module's generated classes.
     *
     * <p>One loader for the module, defined once here. The values a row hands over have to be
     * instances of the classes the answerer applies, so building them and applying them are two ends
     * of one loader rather than two loaders that agree — and the classes are defined once however
     * many behaviors are searched.
     *
     * <p>The classes have to be the measuring ones. A run of classes emitted without the calls that
     * record where it went is a run nothing was recorded of, which reads exactly like a run that
     * went nowhere — so a caller with unmeasured classes must not build one of these, and every
     * combination would otherwise come back missed.
     *
     * @param signatures what each behavior this module reaches takes and answers, and
     *                   {@code contracts} what it states of its answer. Both are what a module's
     *                   tables are held to before one stands anything in, which is the same holding
     *                   a written row's run is under — a search running against a table a written
     *                   row is refused would be certifying rows in an environment nothing else has
     * @param steps how many counted points a row may pass, and how deep a recursive helper may go.
     *              A composed row is not a row anyone wrote, so a model that loops on it is this
     *              search's problem to stop rather than an author's to be told about
     */
    public static RowTrials over(Prepared.ForExamples module,
                              Symbols symbols,
                              SumCases sums,
                              DeclarationKinds kinds,
                              FieldTypes fields,
                              Map<String, ClassFileImage> classes,
                              ClassLoader parent,
                              Map<String, Hir.FnDef> values, GeneratedImplementations generated,
                              Map<ValueName.Behavior, Sig> signatures,
                              Map<ValueName.Behavior, Contract> contracts,
                              ProbeImage probes,
                              EvaluationPolicy steps) {
        MemoryClassLoader loader = new MemoryClassLoader(classes, parent);
        Answerer answerer = Answering.generatedHere().over(generated, loader);
        EnsuresChecks ensures = new EnsuresChecks(loader, contracts, signatures.keySet());
        return (behavior, sig) -> new RowTrials.OfBehavior() {

            @Override
            public Optional<RowTrials.Ran> run(List<Hir.Expr> inputs,
                                               List<RowTrials.AnsweredWith> answers) {
                return ready(inputs, answers).flatMap(ready -> went(ready, probes, steps));
            }

            @Override
            public Optional<AnswerObservation> runReplacing(List<Hir.Expr> inputs,
                                                            List<RowTrials.AnsweredWith> answers,
                                                            Map<Integer, Integer> replacing) {
                return ready(inputs, answers).flatMap(ready -> {
                    Intervention.begin(replacing);
                    try {
                        return applied(ready.applying(), ready.over(), steps, ready.reading());
                    } finally {
                        Intervention.end();
                    }
                });
            }

            @Override
            public AnswerChange change(AnswerObservation was, AnswerObservation now) {
                return reader().change(was, now, sig.outputType());
            }

            private Optional<Ready> ready(List<Hir.Expr> inputs,
                                          List<RowTrials.AnsweredWith> answers) {
                if (!(answerer.of(behavior) instanceof Answerer.Answer.Something applies)) {
                    return Optional.empty();   // nothing applies this behavior, so nothing ran
                }
                return RowTrial.ready(reader(), module, kinds, sums, ensures, applies, behavior,
                        sig, inputs, answers);
            }

            /**
             * One reader per row, the way a written row has one: what a reading builds up while it
             * expands a value is that row's, and a reader kept between them would be a session
             * spanning every candidate of every combination.
             */
            private FixtureReader reader() {
                return new FixtureReader(module, symbols, sums, kinds, fields, values, loader);
            }
        };
    }

    /** A row built and ready to be applied, and what its answer will be read with. */
    private record Ready(Answerer.Applying applying, List<Handed> over, AnswerReading reading) {}

    /**
     * One row, applied, what the probe saw while it was, and what it answered.
     *
     * <p>The recording is begun and read on this thread because the run is on this thread, and it
     * is begun only where there is something to record: classes generated without the calls that
     * write a run down leave no account, which is not the same as an account of a run that reached
     * nothing.
     */
    private static Optional<RowTrials.Ran> went(Ready ready, ProbeImage probes,
                                                EvaluationPolicy steps) {
        // Under the numbering the classes about to be run were emitted with, or not at all where
        // they record nothing. Asked once and answered by the shape: the recording is begun, read
        // and let go inside one arm, so there is no way to end one that was never begun — and what
        // comes back where nothing was watching is no account of a run rather than an account of
        // one that went nowhere.
        return switch (probes) {
            case ProbeImage.Uninstrumented _ ->
                    applied(ready.applying(), ready.over(), steps, ready.reading())
                            .map(answer -> new RowTrials.Ran(new RunRecord.NoAccount(), answer));
            case ProbeImage.Instrumented(NumberingIdentity numbering, var _) -> {
                Probe.begin(numbering);
                try {
                    yield applied(ready.applying(), ready.over(), steps, ready.reading())
                            .map(answer -> new RowTrials.Ran(
                                    new RunRecord.Recorded(Probe.snapshot()), answer));
                } finally {
                    // On every way out, including one nothing here catches. A recording left
                    // installed is where the next reader on this thread would start.
                    Probe.end();
                }
            }
        };
    }

    /**
     * One row, built and gathered for an application, or empty where it could not be: a value
     * that could not be made is a row that never ran.
     */
    private static Optional<Ready> ready(FixtureReader fixtures, Prepared.ForExamples module,
                                         DeclarationKinds kinds, SumCases sums,
                                         EnsuresChecks ensures,
                                         Answerer.Answer.Something applies, String behavior,
                                         Sig sig, List<Hir.Expr> inputs,
                                         List<RowTrials.AnsweredWith> answers) {
        List<BoundaryInput> ins = sig.ins();
        if (inputs.size() != ins.size()) {
            return Optional.empty();   // not a row of this behavior, so this is not the thing to run
        }
        Answerer.Applying applying;
        List<Handed> over;
        try {
            // Built and gathered before anything is recorded. A value that could not be made is a
            // row that never ran, and recording the building would put whatever a fixture's own
            // helpers passed through into what the row is said to have done.
            over = new ArrayList<>(ins.size());
            for (int i = 0; i < ins.size(); i++) {
                Object built = fixtures.built(inputs.get(i), ins.get(i));
                BoundaryInput at = ins.get(i);
                String what = "input " + (i + 1) + " of `" + behavior + "`";
                over.add(new Handed(built, () -> fixtures.neutral(built, at, what)));
            }
            List<DependencyStandin> standins = standingIn(fixtures, module, ensures, answers);
            if (standins == null) {
                // A table the row leans on is not one to stand in with, so there was nothing to
                // apply the behavior with and nothing ran. What is wrong with it is wrong about
                // what the module wrote and is said where the block is.
                return Optional.empty();
            }
            applying = applies.applying(standins);
        } catch (StandinNotBuilt | LinkageError e) {
            // Nothing was applied, and these are the two ways that happens before an application:
            // a stand-in that could not be made, and this compiler's own output not linking. Named
            // rather than taken by category — anything else out of here is this compiler failing at
            // something it does not have a word for, and turning that into a fact about where a row
            // went is how a defect in the runner comes back as a defect in the model.
            return Optional.empty();
        }
        return Optional.of(new Ready(applying, over,
                new AnswerReading(fixtures, sig.outputType(), module.name(), kinds, sums)));
    }

    /**
     * What a run's answer is read with: the value behind the bridge case it may arrive in, read
     * into the form the compiler owns. What a written row's answer is read with as well, so that the
     * same answer from either comes out as the same value.
     */
    private record AnswerReading(FixtureReader fixtures, Type out, String module,
                                 DeclarationKinds kinds, SumCases sums) {

        AnswerReading {
            Objects.requireNonNull(kinds, "an answer is projected by what each declaration is");
            Objects.requireNonNull(sums, "and by the cases each sum has");
        }

        /**
         * The answer, read. A budget running out while it is read leaves an answer that came back
         * and could not be read, which is what it is: the run answered, and where it went is
         * recorded whatever became of the reading.
         */
        AnswerObservation read(Object answered) {
            ObservedValue value;
            try {
                value = fixtures.observed(
                        ExampleVerifier.projected(answered, out, module, kinds, sums));
            } catch (StepLimitExceeded | DepthLimitExceeded e) {
                value = new ObservedValue.Unknown("the budget ran out while the answer was read");
            }
            return new AnswerObservation.Answered(value);
        }
    }

    /**
     * What the candidate stands its target's dependencies in with, built.
     *
     * <p>The values go through the reader this row is being built by, so a dependency's answer is
     * one of this module's own values exactly as an input of the row is. Built here rather than
     * where the candidate was composed, for the reason a row's inputs are: what a search chose is
     * text and a tree, and what an implementation is constructed with is of the loader it came
     * from.
     *
     * <p>One answer for every call where the candidate wrote a value, which is what a row's
     * {@code with} states. A candidate is run to find out where it goes, so a call this reading did
     * not foresee is answered rather than refused — a run that stopped at one would say nothing
     * about that.
     *
     * <p>And the module's table where the candidate leaned on it, dispatching call by call the way
     * it does under a row somebody wrote. Which answer a call gets is then the table's, which is
     * the point: a candidate leaning on the table is a candidate whose way through the body the
     * module's own environment decides, and running it against anything else would certify a row
     * that goes somewhere else once it is pasted in.
     *
     * <p>Null where a table the candidate leans on is not one to stand in with, which is a row that
     * cannot be run rather than one that ran and reached nothing.
     */
    private static List<DependencyStandin> standingIn(FixtureReader fixtures,
                                                      Prepared.ForExamples module,
                                                      EnsuresChecks ensures,
                                                      List<RowTrials.AnsweredWith> answers) {
        List<DependencyStandin> out = new ArrayList<>(answers.size());
        for (RowTrials.AnsweredWith each : answers) {
            switch (each) {
                case RowTrials.AnsweredWith.OnTheRow(var dependency, var signature, var written) -> {
                    Object value = fixtures.buildFixture(written, signature.out()).value();
                    out.add(StandingIn.by(dependency, signature.ins().size(), _ -> value));
                }
                case RowTrials.AnsweredWith.InTheModule(var dependency, var signature) -> {
                    StandingIn.OffATable stood = statedFor(fixtures, module, ensures, dependency,
                            signature);
                    if (stood == null) {
                        return null;
                    }
                    out.add(stood.applies());
                }
            }
        }
        return List.copyOf(out);
    }

    /**
     * The stand-in the module's table gives for {@code dependency}, or null where there is none to
     * give.
     *
     * <p>Asked of the module here rather than carried on the candidate. What a module states is one
     * table however many candidates lean on it, and a candidate carrying a copy would be running
     * against whatever the table said when it was composed.
     */
    private static StandingIn.OffATable statedFor(FixtureReader fixtures,
                                                  Prepared.ForExamples module,
                                                  EnsuresChecks ensures,
                                                  ValueName.Behavior dependency, Sig signature) {
        return module.fakes().declaredFor(dependency)
                instanceof FakeTables.Declaration.One(var stated)
                ? StandingIn.byTheTable(fixtures, ensures, stated, dependency, signature) : null;
    }

    /**
     * Applies the behavior, and says what it answered — or that it was not applied at all, which is
     * the empty answer.
     *
     * <p>A run that aborts still went where it went, so what stopped it is dropped: nothing here is
     * judging the row, and a generator has no expectation for it to have failed against. It answered
     * nothing, and that is what it is said to have answered. What is not a run at all is the
     * implementation being out of reach.
     *
     * <p>The answer is read inside the budget, as a written row's is: reading it walks what the run
     * built, and that walk is counted the way the building was.
     *
     * <p>The budget is let go on every way out, a worker being something the next row would
     * otherwise start inside of.
     */
    private static Optional<AnswerObservation> applied(Answerer.Applying applying,
                                                       List<Handed> over, EvaluationPolicy steps,
                                                       AnswerReading reading) {
        EvaluationContext.begin(steps.stepLimit(), steps.recursionDepthLimit());
        try {
            Object answered;
            try {
                answered = applying.to(over);
            } catch (ImplementationNotReached e) {
                // Not a run at all: the implementation could not be reached to apply. Saying the
                // row did nothing would be saying it went nowhere, and those are different facts.
                return Optional.empty();
            } catch (InvocationFailure e) {
                // It ran and stopped. Where it had got to is what is being asked for, and what
                // stopped it is not.
                //
                // This one and no wider. What the applied code ends with arrives as this, so a
                // throwable that is not one is this compiler failing to reach or drive its own
                // output — and swallowed here it would come back as a candidate that ran and
                // missed, which is a statement about the model. The seam says which failures it
                // has ({@link Answerer.Applying#to}) and those are the ones read.
                return Optional.of(new AnswerObservation.NotAnswered());
            }
            return Optional.of(reading.read(answered));
        } finally {
            EvaluationContext.end();
        }
    }

    private RowTrial() {}
}
