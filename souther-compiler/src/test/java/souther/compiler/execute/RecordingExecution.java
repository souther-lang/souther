package souther.compiler.execute;

import souther.compiler.observe.ArmObservation;
import souther.compiler.observe.RowRun;
import souther.compiler.observe.StatementReading;
import souther.compiler.observe.TableBuild;
import souther.compiler.source.SourceId;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

/**
 * An execution that runs nothing, written to find out what answering the language costs.
 *
 * <p>Not a second evaluator and not the start of one. What it is for is the one thing a reading
 * cannot establish: that every question on this boundary can be taken, and every answer given,
 * without knowing that a Souther program is ever a set of JVM classes. It compiles, and that is the
 * claim.
 *
 * <p>Every method carries {@code @Override}. A question added to the boundary that cannot be
 * answered from here stops this file compiling, which is the point of it.
 */
final class RecordingExecution implements ProgramExecution {

    /** What it was asked, in the words it was asked in. */
    private final List<String> asked = new ArrayList<>();

    List<String> asked() {
        return List.copyOf(asked);
    }

    @Override
    public ConstantOutcome check(ConstantConstruction written) {
        asked.add("constant " + written.typeName() + " written in " + written.writtenIn()
                + " at " + written.pos() + ", of " + written.type()
                + ", over " + written.clauses().size() + " clauses, of " + written.value());
        return new ConstantOutcome.NotEvaluatedHere();
    }

    @Override
    public RowRun run(ExampleExecution about, SourceId source, ArmObservation arms) {
        asked.add("rows of " + read(about) + " written in " + source + ", arms " + arms);
        return new RowRun.NotRunHere();
    }

    /**
     * Every part of the ask, read.
     *
     * <p>A stand-in that took the question and looked at none of it would prove that the boundary
     * can be declared without the machine and not that it can be met: the imports it does not need
     * are the ones for the parts it never opened. So this reads all of them, and what it makes of
     * them is a sentence, because what it is showing is that they can be read at all.
     *
     * <p>The terms are worked with and not quoted. A getter called for the object that comes back
     * would compile against a term whose type this cannot name, and print it — which says the ask
     * carries something, not that an execution can be held to it. Splitting the budget over what
     * was written is this stand-in's own arrangement, and it is what makes the number in the
     * sentence the terms' and not the sentence's. A module that wrote none is given the whole of it
     * rather than divided by nothing.
     */
    private static String read(ExampleExecution about) {
        EvaluationPolicy held = about.policy();
        long written = Math.max(1, about.forExamples().examples().size());
        return about.module()
                + " (" + about.forExamples().examples().size() + " examples"
                + ", " + about.signatures().size() + " behaviors"
                + ", " + about.requirements().size() + " requirement tables"
                + ", " + about.definitions().size() + " definitions"
                + ", " + about.contracts().size() + " contracts"
                + ", names " + (Objects.requireNonNull(about.symbols()) != null)
                + ", " + held.stepLimit() / written + " steps an example"
                + ", " + held.recursionDepthLimit() + " deep"
                + ", given up on after " + held.outerTimeout().toMillis() + "ms)";
    }

    @Override
    public TableBuild fakeTables(ExampleExecution about, SourceId source) {
        asked.add("fakes of " + read(about) + " written in " + source
                + ", " + about.forExamplesWrittenIn(source).examples().size() + " of them here");
        return new TableBuild.NotBuiltHere();
    }

    @Override
    public StatementReading statements(ExampleExecution about) {
        asked.add("statements of " + read(about));
        return new StatementReading.NotReadHere();
    }

    @Override
    public BoundaryValues values(ExampleExecution about) {
        asked.add("values of " + read(about));
        return null;
    }

    @Override
    public RowTrials trials(ExampleExecution about, ArmObservation arms) {
        asked.add("trials of " + read(about) + ", arms " + arms);
        return null;
    }
}
