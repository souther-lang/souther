package souther.compiler.generated;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/** A link failure is the host having no runtime, or this compiler's output being wrong, and only the
 * first is something a reading may go on without. */
class GeneratedLinkageTest {

    @Test
    void aMissingRuntimeClassIsTheRuntimeBeingAbsent() {
        assertTrue(GeneratedLinkage.runtimeAbsent(new NoClassDefFoundError("souther/runtime/Behavior")));
        assertDoesNotThrow(() -> GeneratedLinkage.requireRuntimeAbsent(
                new NoClassDefFoundError("souther.runtime.Sets")));
    }

    @Test
    void aClassThatWillNotVerifyIsNotTheRuntimeBeingAbsent() {
        VerifyError wrong = new VerifyError("Bad type on operand stack");
        assertFalse(GeneratedLinkage.runtimeAbsent(wrong));
        GeneratedLinkage.GeneratedClassDefect defect = assertThrows(
                GeneratedLinkage.GeneratedClassDefect.class,
                () -> GeneratedLinkage.requireRuntimeAbsent(wrong));
        assertSame(wrong, defect.getCause(), "what the JVM said is kept");
        assertInstanceOf(RuntimeException.class, defect, "the command line reports it as a failure");
    }

    @Test
    void aMissingClassOfAnotherLibraryIsNotTheRuntimeBeingAbsent() {
        assertFalse(GeneratedLinkage.runtimeAbsent(new NoClassDefFoundError("net/unit8/raoh/Result")));
        assertFalse(GeneratedLinkage.runtimeAbsent(new NoSuchMethodError("souther.runtime.Sets.repeated")));
        assertFalse(GeneratedLinkage.runtimeAbsent(new NoClassDefFoundError()));
    }
}
