package souther.compiler.codegen;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * The class file writer refuses two different things with one sentence each: a method whose code is
 * longer than 65535 bytes and one whose code is empty share a message, and a constant-pool index past
 * 65535 shares its message with an index of zero. Only one side of each pair is something the author
 * wrote too much of; the other is this compiler emitting nothing, or emitting a reference it never
 * pooled. Reading the number is what tells them apart, and what is not a limit stays an exception.
 */
class AClassfileRefusalIsALimitOnlyWhenTheNumberSaysSoTest {

    @Test
    void codeLongerThanAMethodHoldsIsTheCodeSizeLimit() {
        JvmLimits.Exceeded e = JvmLimits.exceeded(new IllegalArgumentException(
                "Code length 65539 is outside the allowed range in apply(Object)Object"));

        assertEquals(JvmLimits.Limit.CODE_SIZE, e.limit());
        assertEquals(65539, e.measured());
        assertEquals("apply", e.method());
    }

    @Test
    void anEmptyMethodBodyIsNotTheCodeSizeLimit() {
        assertNull(JvmLimits.exceeded(new IllegalArgumentException(
                "Code length 0 is outside the allowed range in decode(Object,Path)Result")));
    }

    @Test
    void anIndexPastWhatAConstantPoolHoldsIsTheConstantPoolLimit() {
        JvmLimits.Exceeded e = JvmLimits.exceeded(new IllegalArgumentException(
                "80031 is not a valid index. Entry: 11 java/util/List.copyOf-"
                        + "(Ljava/util/Collection;)Ljava/util/List;"));

        assertEquals(JvmLimits.Limit.CONSTANT_POOL, e.limit());
        assertEquals(80031, e.measured());
        assertNull(e.method(), "the writer does not say which method it was writing");
    }

    @Test
    void anIndexBelowTheFirstEntryIsNotTheConstantPoolLimit() {
        assertNull(JvmLimits.exceeded(new IllegalArgumentException(
                "0 is not a valid index. Entry: 11 java/lang/Object")));
        assertNull(JvmLimits.exceeded(new IllegalArgumentException(
                "-1 is not a valid index. Entry: 11 java/lang/Object")));
    }

    @Test
    void theLastIndexAConstantPoolHoldsIsNotOverIt() {
        assertNull(JvmLimits.exceeded(new IllegalArgumentException(
                "65535 is not a valid index. Entry: 11 java/lang/Object")));
    }

    @Test
    void anythingElseIsNotALimit() {
        assertNull(JvmLimits.exceeded(new IllegalArgumentException("bytecode offset out of range")));
        assertNull(JvmLimits.exceeded(new IllegalArgumentException()));
    }
}
