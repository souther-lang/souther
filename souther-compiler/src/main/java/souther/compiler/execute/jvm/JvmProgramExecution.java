package souther.compiler.execute.jvm;

import souther.compiler.codegen.Backend;
import souther.compiler.evaluate.EvaluationContext;
import souther.compiler.execute.ConstantConstruction;
import souther.compiler.execute.ConstantOutcome;
import souther.compiler.execute.EvaluationPolicy;
import souther.compiler.execute.ProgramExecution;
import souther.compiler.execute.ValueBuild;
import souther.compiler.execute.WrittenValue;
import souther.compiler.examples.Answering;
import souther.compiler.examples.Deadline;
import souther.compiler.examples.ExampleStatements;
import souther.compiler.examples.FixtureReader;
import souther.compiler.examples.ExampleVerifier;
import souther.compiler.examples.RowTrial;
import souther.compiler.execute.BoundaryValues;
import souther.compiler.execute.ExampleExecution;
import souther.compiler.execute.RowTrials;
import souther.compiler.generated.GeneratedLinkage;
import souther.compiler.generated.MemoryClassLoader;
import souther.compiler.jvm.GeneratedClass;
import souther.compiler.jvm.SoutherJvmAbi;
import souther.compiler.observe.ArmObservation;
import souther.compiler.observe.Observations;
import souther.compiler.observe.RowRun;
import souther.compiler.observe.StatementReading;
import souther.compiler.observe.TableBuild;
import souther.compiler.source.SourceId;
import souther.runtime.ConstraintViolation;
import souther.runtime.InvariantFailure;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.math.BigDecimal;
import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * The implementation ADR-0032 names: the questions are answered by running the program that will
 * ship.
 *
 * <p>Everything the machine needs is here and nowhere above it — the generated class name, the
 * loader it is resolved in, the reflection that calls the check, and which primitive a written
 * constant is passed as. A compiler that reflected over a generated class in the middle of deciding
 * whether it accepts a program was writing one implementation's address into the language's own
 * verdict.
 */
public final class JvmProgramExecution implements ProgramExecution {

    private final JvmProgramImages images;
    private final JvmExampleDeadlines deadlines;

    public JvmProgramExecution(JvmProgramImages images, JvmExampleDeadlines deadlines) {
        if (images == null) {
            throw new IllegalArgumentException("a run of the JVM program needs its classes");
        }
        if (deadlines == null) {
            throw new IllegalArgumentException(
                    "a run of the JVM program needs the deadline it runs under");
        }
        this.images = images;
        this.deadlines = deadlines;
    }

    /**
     * The arrangement this run keeps the wait it was told with.
     *
     * <p>Told and not looked up. The wait is one of the terms in {@code asked}, so this is where it
     * is turned into something that keeps it, and there is no other way for a run here to learn it —
     * which is what stops the boundary saying one wait while the run is given up on at another.
     */
    private souther.compiler.examples.Deadline keeping(ExampleExecution asked) {
        return deadlines.forThisCompile(asked.policy().compilerTimeout());
    }

    @Override
    public RowRun run(ExampleExecution asked, SourceId source, ArmObservation arms) {
        JvmProgramImage image = images.evaluating(asked.module(), arms);
        if (image == null) {
            return new RowRun.NotRunHere();
        }
        Observations observed = ExampleVerifier.check(asked.forExamplesWrittenIn(source),
                asked.symbols(),
                asked.sums(),
                asked.kinds(),
                asked.fieldTypes(),
                asked.signatures(), image.program(), image.published(), asked.requirements(),
                image.around(), asked.definitions(), keeping(asked), asked.policy(),
                // What applies a behavior here is what this compile emitted. A compile has nothing
                // else to run a row against; something supplied from outside one arrives through
                // the same seam and brings its own classes.
                Answering.generatedHere(), asked.contracts());
        return new RowRun.Ran(observed);
    }

    @Override
    public TableBuild fakeTables(ExampleExecution asked, SourceId source) {
        if (ExampleStatements.tablesBuiltIn(asked.forExamples(), asked.signatures(), source).isEmpty()) {
            // Nothing this source states is a table this source builds, so there is nothing here
            // that went unbuilt. Asked the other way round — is there a program to build against —
            // a file that wrote no fake at all would answer that its tables could not be built,
            // and a caller reading that as "this source was not answered for" would lose whatever
            // its rows had to say.
            return new TableBuild.Built(List.of());
        }
        JvmProgramImage image = images.evaluating(asked.module(), ArmObservation.OMIT);
        if (image == null) {
            return new TableBuild.NotBuiltHere();
        }
        // The classes alone. Nothing here applies a behavior, so what the compile implemented is not
        // a question this asks.
        return new TableBuild.Built(ExampleStatements.fakeTables(asked.forExamples(), asked.symbols(),
                asked.sums(),
                asked.kinds(),
                asked.fieldTypes(),
                asked.signatures(), image.program().classes(), image.around(), asked.definitions(),
                source, keeping(asked), asked.policy(), asked.contracts()));
    }

    @Override
    public StatementReading statements(ExampleExecution asked) {
        JvmProgramImage image = images.evaluating(asked.module(), ArmObservation.OMIT);
        if (image == null) {
            return new StatementReading.NotReadHere();
        }
        // The rows of the modules this one stands in for a behavior of, as those modules write
        // them. Their executions are not taken: the values are built on this image's loader, which
        // carries every module this one reaches, so the two sides of a comparison are of one
        // execution and the equality that decides it is the language's own.
        Map<String, ExampleStatements.Declaring> declaring = new LinkedHashMap<>();
        asked.declaring().forEach((name, reading) -> declaring.put(name,
                new ExampleStatements.Declaring(reading.forExamples(), reading.symbols(),
                        reading.sums(), reading.kinds(), reading.fieldTypes(),
                        reading.definitions())));
        return new StatementReading.Read(ExampleStatements.disagreements(asked.forExamples(),
                asked.symbols(), asked.sums(), asked.kinds(), asked.fieldTypes(),
                asked.signatures(), image.program().classes(), image.around(),
                asked.definitions(), keeping(asked), asked.policy(), asked.contracts(),
                declaring));
    }

    @Override
    public BoundaryValues values(ExampleExecution asked) {
        // The classes alone: building a value applies no behavior, so what the compile implemented
        // is not a question this asks.
        //
        // And uncounted, said outright rather than taken from what the build happens to be
        // measuring. Which arms a row goes through is recorded by instrumenting the bodies, and a
        // value is built by the decoders without one of them running — so asking for the recorded
        // classes here would make composing a value fail wherever the plan and the bodies do not
        // line up, which is a fault in a measurement nothing here is making.
        JvmProgramImage image = images.evaluating(asked.module(), ArmObservation.OMIT);
        return image == null ? null
                : FixtureReader.constructing(asked.forExamples(), asked.symbols(),
                        asked.sums(), asked.kinds(), asked.fieldTypes(),
                        image.program().classes(), image.around(), asked.definitions());
    }

    @Override
    public RowTrials trials(ExampleExecution asked, ArmObservation arms) {
        JvmProgramImage image = images.evaluating(asked.module(), arms);
        if (image == null || image.program().implementations() == null) {
            return null;
        }
        return RowTrial.over(asked.forExamples(), asked.symbols(), asked.sums(), asked.kinds(),
                asked.fieldTypes(),
                image.program().classes(),
                image.around(), asked.definitions(), image.program().implementations(),
                asked.signatures(), asked.contracts(),
                image.program().probes(), asked.policy());
    }

    @Override
    public ConstantOutcome check(ConstantConstruction written) {
        ClassLoader loader = images.compileTimeLoader(written.writtenIn());
        if (loader == null) {
            return new ConstantOutcome.NotEvaluatedHere();
        }
        Class<?> ctfe;
        try {
            ctfe = Class.forName(SoutherJvmAbi.nameOf(new GeneratedClass.Ctfe(
                    new GeneratedClass.Value(written.type()))).binaryName(), true, loader);
            if ((boolean) ctfe.getMethod("check", parameterOf(written.value()))
                    .invoke(null, argumentOf(written.value()))) {
                return new ConstantOutcome.Holds();
            }
        } catch (ReflectiveOperationException | LinkageError e) {
            // Not this compiler failing to say something. Where the check cannot be run here the
            // language leaves the construction to the check that runs when the program does, which
            // is ADR-0032's own degradation and one of the three answers. A check that was
            // generated wrongly is this compiler failing and is not left to the program, and it
            // arrives wrapped where the call reached it.
            GeneratedLinkage.rejectDefect(e);
            return new ConstantOutcome.NotEvaluatedHere();
        }
        return new ConstantOutcome.Violates(failingClause(ctfe, written));
    }

    @Override
    public Map<String, ConstantOutcome> build(ValueBuild asked, EvaluationPolicy policy) {
        Map<String, ConstantOutcome> outcomes = new LinkedHashMap<>();
        // The classes a row is evaluated with: they count the steps and the depth they spend, so a
        // value that does not stop is held to the same figures a row is.
        JvmProgramImage image = images.evaluating(asked.writtenIn(), ArmObservation.OMIT);
        if (image == null) {
            asked.inOrder().forEach(each ->
                    outcomes.put(each.name(), new ConstantOutcome.NotEvaluatedHere()));
            return outcomes;
        }
        ClassLoader loader = new MemoryClassLoader(image.program().classes(), image.around());
        Deadline deadline = deadlines.forThisCompile(policy.compilerTimeout());
        Map<String, Object> built = new HashMap<>();
        for (ValueBuild.Step each : asked.inOrder()) {
            Object[] handed = new Object[each.handed().size()];
            boolean everyOneBuilt = true;
            for (int i = 0; i < handed.length; i++) {
                everyOneBuilt &= built.containsKey(each.handed().get(i));
                handed[i] = built.get(each.handed().get(i));
            }
            outcomes.put(each.name(), everyOneBuilt
                    ? building(asked.writtenIn(), each, handed, loader, deadline, policy, built)
                    : new ConstantOutcome.NotEvaluatedHere());
        }
        return outcomes;
    }

    /**
     * One value, built within what {@code policy} allows a run, and kept in {@code built} where it
     * was.
     *
     * <p>Only a broken invariant is a violation. The carrier the abort leaves by is one class for
     * every constraint of the language's, so what a value that ended is told apart by is the failure
     * it carries and not its class.
     */
    private static ConstantOutcome building(String module, ValueBuild.Step value, Object[] handed,
                                            ClassLoader loader, Deadline deadline,
                                            EvaluationPolicy policy, Map<String, Object> built) {
        Deadline.Outcome<Object> ran = deadline.given(
                new Deadline.Work.Value(value.name(), value.pos()), () -> {
                    EvaluationContext.begin(policy.stepLimit(), policy.recursionDepthLimit());
                    try {
                        return invoked(module, value.name(), handed, loader);
                    } finally {
                        EvaluationContext.end();
                    }
                });
        return switch (ran) {
            case Deadline.Outcome.Finished<Object>(Object made) -> {
                built.put(value.name(), made);
                yield new ConstantOutcome.Holds();
            }
            case Deadline.Outcome.Overran<Object>(Runnable abandon) -> {
                abandon.run();
                yield new ConstantOutcome.NotEvaluatedHere();
            }
            case Deadline.Outcome.Threw<Object>(Throwable cause) -> {
                Throwable ended = cause instanceof InvocationTargetException call
                        && call.getCause() != null ? call.getCause() : cause;
                yield ended instanceof ConstraintViolation violation
                        && violation.failure() instanceof InvariantFailure broken
                        ? new ConstantOutcome.Violates(Optional.ofNullable(broken.clause()))
                        : new ConstantOutcome.NotEvaluatedHere();
            }
        };
    }

    /** The value as the method the module emits for it answers it, given what it is handed. */
    private static Object invoked(String module, String name, Object[] handed, ClassLoader loader)
            throws ReflectiveOperationException {
        Class<?> fns = Class.forName(SoutherJvmAbi.nameOf(
                new GeneratedClass.Helpers(module)).binaryName(), true, loader);
        Class<?>[] taken = new Class<?>[handed.length];
        Arrays.fill(taken, Object.class);
        Method method = fns.getDeclaredMethod(Backend.helperMethod(name), taken);
        method.setAccessible(true);
        return method.invoke(null, handed);
    }

    /**
     * The clause the value breaks, or none where the clause carries no name of its own or the check
     * for it cannot be run.
     *
     * <p>The clauses are asked one at a time in the order they are declared, so the one named is the
     * one a construction at run time would report: that construction refines the same checks in the
     * same order and stops at the first that does not hold.
     */
    private static Optional<String> failingClause(Class<?> ctfe, ConstantConstruction written) {
        List<ConstantConstruction.Clause> clauses = written.clauses();
        for (int i = 0; i < clauses.size(); i++) {
            try {
                if (!(boolean) ctfe.getMethod(Backend.clauseCheck(i), parameterOf(written.value()))
                        .invoke(null, argumentOf(written.value()))) {
                    return clauses.get(i).name();
                }
            } catch (ReflectiveOperationException | LinkageError e) {
                GeneratedLinkage.rejectDefect(e);
                return Optional.empty();
            }
        }
        return Optional.empty();
    }

    /** What the generated check declares the constant as. */
    private static Class<?> parameterOf(WrittenValue value) {
        return switch (value) {
            case WrittenValue.Whole _ -> long.class;
            case WrittenValue.Truth _ -> boolean.class;
            case WrittenValue.Text _ -> String.class;
            case WrittenValue.Decimal _ -> BigDecimal.class;
        };
    }

    /** The same constant as the object a reflective call is handed. */
    private static Object argumentOf(WrittenValue value) {
        return switch (value) {
            case WrittenValue.Whole(long whole) -> whole;
            case WrittenValue.Truth(boolean truth) -> truth;
            case WrittenValue.Text(String text) -> text;
            case WrittenValue.Decimal(BigDecimal decimal) -> decimal;
        };
    }
}
