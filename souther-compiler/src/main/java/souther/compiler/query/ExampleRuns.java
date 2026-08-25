package souther.compiler.query;

import souther.compiler.execute.ExampleExecution;
import souther.compiler.observe.ArmObservation;
import souther.compiler.examples.Answering;
import souther.compiler.examples.ExampleVerifier;
import souther.compiler.generated.EvaluationArtifact;

/**
 * What a run of a module's rows is made of, assembled once for a caller that runs them itself.
 *
 * <p>{@link Output.Examples} reads the same environment to run a module's rows in bulk, and this is
 * here because the two runs differ in who owns the loop and in nothing else: a row's fixtures are
 * decoded through their derived decoders against this module's symbols and this compile's classes
 * whichever of them asks for it. Both read it from {@link ExampleExecutions}, so what "this module
 * can have its examples run" means is one answer. What is not shared is what a bulk run adds — which source the rows
 * were written in, whether the arms are recorded, and how an absent answer travels —
 * none of which a caller running one row at a time has a question about.
 *
 * <p>Reached from outside the compiler, so what it hands back is the thing rows are run against and
 * not a report. Whether a row that failed fails a build is not knowledge of the model.
 */
public final class ExampleRuns {

    private ExampleRuns() {
    }

    /**
     * The module's rows, ready to be run one at a time against what {@code answering} gives.
     *
     * <p>Every argument comes from the compilation and none is a caller's to choose. What an
     * implementation is held to is the module as this reading of the source has it, which is the
     * whole reason the source is read at the time the run happens.
     */
    public static ExampleVerifier evaluating(Db db, String module, Answering answering) {
        ExampleExecution asked = ExampleExecutions.of(db, module);
        if (asked == null) {
            throw new IllegalStateException("`" + module + "` did not check, so it has no rows to"
                    + " run");
        }
        EvaluationArtifact artifact = db
                .ask(new Output.EvaluationLinked(module, ArmObservation.OMIT)).value();
        if (artifact == null) {
            throw new IllegalStateException("`" + module + "` emitted nothing to run its rows"
                    + " against");
        }
        return ExampleVerifier.evaluating(
                asked.rows(),
                asked.symbols(),
                asked.signatures(),
                artifact,
                () -> Output.declarationsRead(db),
                asked.requirements(),
                Output.evaluationLoader(db),
                asked.definitions(),
                asked.deadline(),
                asked.policy(),
                answering,
                asked.contracts());
    }
}
