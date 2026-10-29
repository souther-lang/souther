package souther.compiler.generated;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.SourcePos;
import souther.compiler.evaluate.EvaluationContext;
import souther.compiler.evaluate.StepLimitExceeded;
import souther.compiler.examples.Deadline;
import souther.compiler.examples.ImplementationNotReached;
import souther.compiler.examples.InvocationFailure;
import souther.compiler.execute.jvm.JvmDeadlines;

import java.lang.reflect.InvocationTargetException;
import java.time.Duration;
import java.util.concurrent.ExecutionException;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/** A failure out of a generated class is the host having no runtime, the evaluated code failing, or
 * this compiler's output being wrong, and only the last is the compiler's to report. */
class GeneratedLinkageTest {

    @Test
    void aMissingRuntimeClassIsNotADefect() {
        assertTrue(GeneratedLinkage.runtimeAbsent(new NoClassDefFoundError("souther/runtime/Behavior")));
        assertDoesNotThrow(() -> GeneratedLinkage.rejectDefect(
                new NoClassDefFoundError("souther.runtime.Sets")));
    }

    @Test
    void aClassThatWillNotVerifyIsADefect() {
        VerifyError wrong = new VerifyError("Bad type on operand stack");
        assertFalse(GeneratedLinkage.runtimeAbsent(wrong));
        GeneratedLinkage.GeneratedClassDefect defect = assertThrows(
                GeneratedLinkage.GeneratedClassDefect.class,
                () -> GeneratedLinkage.rejectDefect(wrong));
        assertSame(wrong, defect.getCause(), "what the JVM said is kept");
        assertInstanceOf(RuntimeException.class, defect, "the command line reports it as a failure");
    }

    @Test
    void aMissingClassOfAnotherLibraryIsADefect() {
        assertThrows(GeneratedLinkage.GeneratedClassDefect.class, () -> GeneratedLinkage.rejectDefect(
                new NoClassDefFoundError("net/unit8/raoh/Result")));
        assertThrows(GeneratedLinkage.GeneratedClassDefect.class, () -> GeneratedLinkage.rejectDefect(
                new NoSuchMethodError("souther.runtime.Sets.repeated")));
    }

    /** A reflective call wraps whatever the callee threw, an {@code Error} included, so the link
     * failure arrives as the cause of the exception a caller catches. */
    @Test
    void aDefectInsideAReflectiveCallIsStillADefect() {
        VerifyError wrong = new VerifyError("Bad type on operand stack");
        GeneratedLinkage.GeneratedClassDefect defect = assertThrows(
                GeneratedLinkage.GeneratedClassDefect.class,
                () -> GeneratedLinkage.rejectDefect(new InvocationTargetException(wrong)));
        assertSame(wrong, defect.getCause());
        assertThrows(GeneratedLinkage.GeneratedClassDefect.class, () -> GeneratedLinkage.rejectDefect(
                new ExecutionException(new InvocationTargetException(wrong))));
    }

    @Test
    void theRuntimeBeingAbsentInsideAReflectiveCallIsNotADefect() {
        assertDoesNotThrow(() -> GeneratedLinkage.rejectDefect(new InvocationTargetException(
                new NoClassDefFoundError("souther/runtime/Sets"))));
    }

    /** An initializer that threw is the evaluated code failing; what it failed with is its cause. */
    @Test
    void anInitializerThatThrewIsReadByItsCause() {
        assertDoesNotThrow(() -> GeneratedLinkage.rejectDefect(
                new ExceptionInInitializerError(new IllegalStateException("a value that does not hold"))));
        assertDoesNotThrow(() -> GeneratedLinkage.rejectDefect(new InvocationTargetException(
                new ExceptionInInitializerError(new StackOverflowError()))));
        assertThrows(GeneratedLinkage.GeneratedClassDefect.class, () -> GeneratedLinkage.rejectDefect(
                new ExceptionInInitializerError(new VerifyError("Bad type on operand stack"))));
    }

    @Test
    void aClassWhoseInitializerAlreadyFailedIsNotADefectItself() {
        assertDoesNotThrow(() -> GeneratedLinkage.rejectDefect(
                new NoClassDefFoundError("Could not initialize class repro.Values")));
    }

    @Test
    void aDefectAlreadyClassifiedIsRaisedAsItself() {
        GeneratedLinkage.GeneratedClassDefect first = assertThrows(
                GeneratedLinkage.GeneratedClassDefect.class,
                () -> GeneratedLinkage.rejectDefect(new VerifyError("x")));
        assertSame(first, assertThrows(GeneratedLinkage.GeneratedClassDefect.class,
                () -> GeneratedLinkage.rejectDefect(new IllegalStateException("a layer's own", first))));
    }

    /** Every reader of what a generated method ended with receives it through this carrier, so the
     * carrier is where a link failure stops being something a row ended with. */
    @Test
    void whatAGeneratedMethodEndedWithIsNeverALinkFailureOfTheClass() {
        VerifyError wrong = new VerifyError("Bad type on operand stack");
        GeneratedLinkage.GeneratedClassDefect defect = assertThrows(
                GeneratedLinkage.GeneratedClassDefect.class, () -> new InvocationFailure(wrong));
        assertSame(wrong, defect.getCause());
        assertThrows(GeneratedLinkage.GeneratedClassDefect.class, () -> new InvocationFailure(
                new ExceptionInInitializerError(wrong)));
        InvocationFailure ended = new InvocationFailure(new StackOverflowError());
        assertInstanceOf(StackOverflowError.class, ended.getCause());
        assertInstanceOf(InvocationFailure.class, new InvocationFailure(
                new NoClassDefFoundError("Could not initialize class repro.Values")));
    }

    @Test
    void theRuntimeBeingAbsentIsReadThroughTheCausesLikeADefectIs() {
        assertTrue(GeneratedLinkage.runtimeAbsent(new InvocationTargetException(
                new NoClassDefFoundError("souther/runtime/Sets"))));
        assertFalse(GeneratedLinkage.runtimeAbsent(new InvocationTargetException(
                new VerifyError("Bad type on operand stack"))));
        assertFalse(GeneratedLinkage.runtimeAbsent(null));
    }

    /** The outcome of work that was given a deadline is received by six readers, each of which used
     * to decide for itself what a link failure out of the worker was. */
    @Test
    void workThatEndedInALinkFailureHasNoOutcomeToRead() {
        VerifyError wrong = new VerifyError("Bad type on operand stack");
        SourcePos at = new SourcePos(1, 1);
        Deadline deadline = JvmDeadlines.of(Duration.ofSeconds(30));

        GeneratedLinkage.GeneratedClassDefect defect = assertThrows(
                GeneratedLinkage.GeneratedClassDefect.class,
                () -> deadline.given(new Deadline.Work.Table("t", at), () -> {
                    throw new InvocationTargetException(wrong);
                }));
        assertSame(wrong, defect.getCause());

        Deadline.Outcome<Object> stopped = deadline.given(new Deadline.Work.Table("t", at), () -> {
            throw new IllegalStateException("a value that does not hold");
        });
        assertInstanceOf(Deadline.Outcome.Threw.class, stopped);
    }

    @Test
    void aClassThatWillNotLinkIsNotAWayOfNotReachingAnImplementation() {
        VerifyError wrong = new VerifyError("Bad type on operand stack");
        assertThrows(GeneratedLinkage.GeneratedClassDefect.class,
                () -> new ImplementationNotReached("x", new InvocationTargetException(wrong)));
        assertInstanceOf(ImplementationNotReached.class,
                new ImplementationNotReached("x", new NoSuchMethodException("apply")));
    }

    /** A catch that turns a failure into "this value cannot be built" asks this, and so reads
     * neither a stop nor a class that does not link as the value. */
    @Test
    void aFailureThatSaysNothingAboutTheValueIsRaisedAsItself() {
        VerifyError wrong = new VerifyError("Bad type on operand stack");
        assertThrows(GeneratedLinkage.GeneratedClassDefect.class,
                () -> EvaluationContext.rethrowUnlessAboutTheValue(new InvocationTargetException(wrong)));
        assertSame(StepLimitExceeded.INSTANCE, assertThrows(StepLimitExceeded.class,
                () -> EvaluationContext.rethrowUnlessAboutTheValue(
                        new InvocationTargetException(StepLimitExceeded.INSTANCE))));
        assertDoesNotThrow(() -> EvaluationContext.rethrowUnlessAboutTheValue(
                new IllegalStateException("a value that cannot be built")));
        assertDoesNotThrow(() -> EvaluationContext.rethrowUnlessAboutTheValue(
                new NoClassDefFoundError("souther/runtime/Sets")));
    }

    /** Going on from a link failure by recording that nothing could be observed says the runtime was
     * not there, and that is all a return from this may be taken to mean. */
    @Test
    void onlyTheRuntimeBeingAbsentLetsACatchGoOn() {
        assertDoesNotThrow(() -> EvaluationContext.rethrowUnlessTheRuntimeIsAbsent(
                new InvocationTargetException(new NoClassDefFoundError("souther/runtime/Sets"))));

        ExceptionInInitializerError initializer = new ExceptionInInitializerError(
                new IllegalStateException("a static that did not hold"));
        IllegalStateException raised = assertThrows(IllegalStateException.class,
                () -> EvaluationContext.rethrowUnlessTheRuntimeIsAbsent(initializer));
        assertSame(initializer, raised.getCause(), "what the initializer threw is kept");

        assertThrows(IllegalStateException.class, () -> EvaluationContext.rethrowUnlessTheRuntimeIsAbsent(
                new NoClassDefFoundError("Could not initialize class repro.Values")));
        assertThrows(GeneratedLinkage.GeneratedClassDefect.class,
                () -> EvaluationContext.rethrowUnlessTheRuntimeIsAbsent(new VerifyError("x")));
        assertSame(StepLimitExceeded.INSTANCE, assertThrows(StepLimitExceeded.class,
                () -> EvaluationContext.rethrowUnlessTheRuntimeIsAbsent(
                        new ExceptionInInitializerError(StepLimitExceeded.INSTANCE))));
    }

    @Test
    void aFailureThatIsNotALinkFailureIsLeftToItsReader() {
        assertDoesNotThrow(() -> GeneratedLinkage.rejectDefect(new IllegalStateException("x")));
        assertDoesNotThrow(() -> GeneratedLinkage.rejectDefect(new StackOverflowError()));
    }

    @Test
    void aCycleOfCausesEnds() {
        RuntimeException a = new RuntimeException("a");
        RuntimeException b = new RuntimeException("b", a);
        a.initCause(b);
        assertDoesNotThrow(() -> GeneratedLinkage.rejectDefect(a));
    }
}
