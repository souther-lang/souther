package souther.compiler.partition;

import souther.compiler.check.AnalysisBody;
import souther.compiler.core.Core;

/**
 * What one elaboration holds of one behavior's body.
 *
 * <p>Three answers, because an absent body is two different facts and a reader of the tree alone
 * cannot tell them apart. A behavior the model gives no body to has nothing to read and a reading
 * of it is complete at once; one the model gives a body to and this elaboration has none of was
 * never read, and what its rules say is unknown rather than nothing. Answered with a tree or a
 * {@code null}, the second reads as the first, and every measure downstream goes on to say what the
 * body states on the strength of not having looked.
 *
 * <p><b>Classified before anything reads the contents.</b> Which of the three it is rests on the
 * declarations and on which bodies the elaboration holds, and neither of those is a question about
 * what a body says — so it is settled once, here, and what interprets a body is handed an answer
 * rather than a tree that might be missing. That is what keeps the reading of the contents from
 * being the place the two absences are told apart, which is where they stopped being told apart.
 */
public sealed interface BodyReading {

    /**
     * The elaboration holds it.
     *
     * <p>{@code analysis} may still be absent. What the analysis reads is its own representation of
     * the body, and a body can come out with none — which is a fact about that representation and
     * not about whether the body is here, so it is not one of the three above.
     */
    record Read(Core emitted, AnalysisBody analysis) implements BodyReading {}

    /**
     * The model gives this behavior no body: something outside supplies it, or nothing does yet.
     *
     * <p>A reading of what its rules divide is complete and empty, because there are no rules to
     * read. This is the answer a measure may draw a conclusion from.
     */
    record NoBody() implements BodyReading {}

    /**
     * The model gives it a body and this elaboration has none.
     *
     * <p>What may be run of a module is a closure over its implementations, so an image holds some
     * of a module's bodies and not others. Nothing read this one: the geometry its declarations and
     * its clauses give is still there to be had, and what its own rules add to that is unknown. A
     * measure over it is short of a reading rather than short of nothing.
     */
    record NotInElaboration() implements BodyReading {}
}
