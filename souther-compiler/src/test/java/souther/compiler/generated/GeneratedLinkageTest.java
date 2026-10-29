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
        assertFalse(((Throwable) defect) instanceof Exception,
                "an Error, so that no catch of an exception a row can throw takes it for an answer");
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

    /** A link failure does not say whose class it was, so whoever ran the code decides, and what is
     * carried out afterwards has been decided. The carrier itself decides nothing: the code it
     * carries out may be a supplied implementation's. */
    @Test
    void whatWasCarriedOutOfAppliedCodeIsNotJudgedAgain() {
        NoSuchMethodError theirs = new NoSuchMethodError("a driver the supplied query calls");
        InvocationFailure carried = new InvocationFailure(theirs);
        assertSame(theirs, carried.getCause());

        assertDoesNotThrow(() -> GeneratedLinkage.rejectDefect(carried));
        assertDoesNotThrow(() -> GeneratedLinkage.rejectDefect(
                new ExecutionException(carried)), "nor under whatever carried it on");
        assertDoesNotThrow(() -> GeneratedLinkage.rejectDefect(
                new ImplementationNotReached("x", new VerifyError("the other build's decoder"))));
    }

    /** The generated code of this compile is the one thing the carrier is told is its own. */
    @Test
    void whatGeneratedCodeOfThisCompileEndedWithIsJudgedBeforeItIsCarried() {
        VerifyError wrong = new VerifyError("Bad type on operand stack");
        GeneratedLinkage.GeneratedClassDefect defect = assertThrows(
                GeneratedLinkage.GeneratedClassDefect.class,
                () -> InvocationFailure.ofGeneratedCode(wrong));
        assertSame(wrong, defect.getCause());

        InvocationFailure ended = InvocationFailure.ofGeneratedCode(new StackOverflowError());
        assertInstanceOf(StackOverflowError.class, ended.getCause());
        assertDoesNotThrow(() -> InvocationFailure.ofGeneratedCode(
                new NoClassDefFoundError("Could not initialize class repro.Values")));
    }

    /** A carrier found above a defect is not what hides it: the walk goes outward in. */
    @Test
    void aDefectAboveACarrierIsStillADefect() {
        InvocationFailure carried = new InvocationFailure(new NoSuchMethodError("theirs"));
        VerifyError ours = new VerifyError("Bad type on operand stack");
        ours.initCause(carried);
        assertThrows(GeneratedLinkage.GeneratedClassDefect.class,
                () -> GeneratedLinkage.rejectDefect(ours));
        assertDoesNotThrow(() -> new Deadline.Outcome.Threw<>(carried),
                "work that ended in a supplied implementation's failure has an outcome to read");
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

    /** For the catch that cannot say whose a failure is: it finds a defect something below judged,
     * under whatever carried it, and judges nothing itself. */
    @Test
    void aDefectAlreadyFoundIsFoundUnderAnyWrapperAndNothingElseIsJudged() {
        GeneratedLinkage.GeneratedClassDefect found = assertThrows(
                GeneratedLinkage.GeneratedClassDefect.class,
                () -> GeneratedLinkage.rejectDefect(new VerifyError("x")));

        assertSame(found, assertThrows(GeneratedLinkage.GeneratedClassDefect.class,
                () -> GeneratedLinkage.rethrowClassified(new InvocationTargetException(found))));
        assertDoesNotThrow(() -> GeneratedLinkage.rethrowClassified(new VerifyError("not yet judged")));
        assertDoesNotThrow(() -> GeneratedLinkage.rethrowClassified(null));
    }

    /** Generated code that calls back into the compiler can have a defect thrown through it, and
     * what carries that out of a supplied implementation holds it as its cause. */
    @Test
    void aDefectUnderAnAttributedCarrierIsStillFound() {
        GeneratedLinkage.GeneratedClassDefect found = assertThrows(
                GeneratedLinkage.GeneratedClassDefect.class,
                () -> GeneratedLinkage.rejectDefect(new VerifyError("x")));

        assertSame(found, assertThrows(GeneratedLinkage.GeneratedClassDefect.class,
                () -> GeneratedLinkage.rejectDefect(new InvocationFailure(found))));
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
