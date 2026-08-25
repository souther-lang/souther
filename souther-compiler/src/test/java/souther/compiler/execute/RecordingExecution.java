package souther.compiler.execute;

import souther.compiler.observe.ArmObservation;
import souther.compiler.observe.RowRun;
import souther.compiler.observe.StatementReading;
import souther.compiler.observe.TableBuild;
import souther.compiler.source.SourceId;

import java.util.ArrayList;
import java.util.List;

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
                + " over " + written.clauses().size() + " clauses");
        return new ConstantOutcome.NotEvaluatedHere();
    }

    @Override
    public RowRun run(ExampleExecution about, SourceId source, ArmObservation arms) {
        asked.add("rows of " + about.module() + " written in " + source + ", arms " + arms);
        return new RowRun.NotRunHere();
    }

    @Override
    public TableBuild fakeTables(ExampleExecution about, SourceId source) {
        asked.add("fakes of " + about.module() + " written in " + source);
        return new TableBuild.NotBuiltHere();
    }

    @Override
    public StatementReading statements(ExampleExecution about) {
        asked.add("statements of " + about.module());
        return new StatementReading.NotReadHere();
    }

    @Override
    public BoundaryValues values(ExampleExecution about) {
        asked.add("values of " + about.module());
        return null;
    }

    @Override
    public RowTrials trials(ExampleExecution about, ArmObservation arms) {
        asked.add("trials of " + about.module() + ", arms " + arms);
        return null;
    }
}
