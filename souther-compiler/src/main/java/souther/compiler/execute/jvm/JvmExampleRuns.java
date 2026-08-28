package souther.compiler.execute.jvm;

import souther.compiler.examples.Answering;
import souther.compiler.examples.Deadline;
import souther.compiler.examples.ExampleVerifier;
import souther.compiler.execute.ExampleExecution;
import souther.compiler.observe.ArmObservation;

/**
 * A run of one module's rows against an implementation supplied from outside Souther.
 *
 * <p>Beside {@link JvmProgramExecution} and not on it. What the language asks is whether its rows
 * hold, and the answer to that is the program this compile emitted; what this is for is a caller
 * that brings its own answerer — a Java object implementing an injected behavior — and wants the
 * module's rows run against it. That is not the same question with a parameter added. It is a
 * binding of Java to Souther, and {@link Answering} says so in its own face: what it hands back is
 * made from a manifest of generated implementations and a loader, which no other implementation of
 * an execution would have.
 *
 * <p>So it is not a second way to ask what acceptance asks. It is reached by the Java-facing
 * {@code SoutherExamples} integration and by nothing that decides whether a program is accepted; a
 * caller that wanted the compile's own answer asks the capability.
 */
public final class JvmExampleRuns {

    private JvmExampleRuns() {}

    /**
     * The module's rows, ready to be run one at a time against what {@code answering} gives.
     *
     * <p>Everything but the answerer comes from the compile. What an implementation is held to is
     * the module as this reading of the source has it, which is the whole reason the source is read
     * at the time the run happens.
     *
     * <p>{@code deadline} is asked for beside the reading rather than taken out of it. What a row is
     * held to crosses as terms; the arrangement that keeps them is this implementation's, and here
     * it is the caller's own — a row driven one at a time from Java hands its applications back to
     * the thread that asked.
     *
     * @throws IllegalStateException where this compile emitted nothing to run the rows against
     */
    public static ExampleVerifier evaluating(JvmProgramImages images, ExampleExecution asked,
                                             Deadline deadline, Answering answering) {
        JvmProgramImage image = images.evaluating(asked.module(), ArmObservation.OMIT);
        if (image == null) {
            throw new IllegalStateException("`" + asked.module() + "` emitted nothing to run its"
                    + " rows against");
        }
        return ExampleVerifier.evaluating(asked.rows(), asked.symbols(), asked.signatures(),
                image.program(), image.published(), asked.requirements(), image.around(),
                asked.definitions(), deadline, asked.policy(), answering,
                asked.contracts());
    }
}
