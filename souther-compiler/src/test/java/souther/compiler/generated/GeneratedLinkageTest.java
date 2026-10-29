package souther.compiler.generated;

import org.junit.jupiter.api.Test;
import souther.compiler.examples.InvocationFailure;

import java.lang.reflect.InvocationTargetException;
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
