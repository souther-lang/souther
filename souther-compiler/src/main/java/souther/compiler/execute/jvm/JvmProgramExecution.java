package souther.compiler.execute.jvm;

import souther.compiler.codegen.Backend;
import souther.compiler.execute.ConstantConstruction;
import souther.compiler.execute.ConstantOutcome;
import souther.compiler.execute.ProgramExecution;
import souther.compiler.execute.WrittenValue;
import souther.compiler.examples.Answering;
import souther.compiler.examples.ExampleVerifier;
import souther.compiler.execute.ExampleExecution;
import souther.compiler.jvm.GeneratedClass;
import souther.compiler.jvm.SoutherJvmAbi;
import souther.compiler.observe.ArmObservation;
import souther.compiler.observe.Observations;
import souther.compiler.observe.RowRun;
import souther.compiler.source.SourceId;

import java.math.BigDecimal;
import java.util.List;
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

    public JvmProgramExecution(JvmProgramImages images) {
        if (images == null) {
            throw new IllegalArgumentException("a run of the JVM program needs its classes");
        }
        this.images = images;
    }

    @Override
    public RowRun run(ExampleExecution asked, SourceId source, ArmObservation arms) {
        JvmProgramImage image = images.evaluating(asked.module(), arms);
        if (image == null) {
            return new RowRun.NotRunHere();
        }
        Observations observed = ExampleVerifier.check(asked.rowsWrittenIn(source), asked.symbols(),
                asked.signatures(), image.program(), image.published(), asked.requirements(),
                image.around(), asked.definitions(), asked.deadline(), asked.policy(),
                // What applies a behavior here is what this compile emitted. A compile has nothing
                // else to run a row against; something supplied from outside one arrives through
                // the same seam and brings its own classes.
                Answering.generatedHere(), asked.contracts());
        return new RowRun.Ran(observed);
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
        } catch (ReflectiveOperationException | LinkageError _) {
            // Not this compiler failing to say something. Where the check cannot be loaded or run
            // here the language leaves the construction to the check that runs when the program
            // does, which is ADR-0032's own degradation and one of the three answers.
            return new ConstantOutcome.NotEvaluatedHere();
        }
        return new ConstantOutcome.Violates(failingClause(ctfe, written));
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
            } catch (ReflectiveOperationException | LinkageError _) {
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
