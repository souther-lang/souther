package souther.compiler.codegen;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassFile;
import java.lang.constant.ClassDesc;
import java.lang.constant.ConstantDescs;
import java.lang.constant.MethodTypeDesc;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * The class file writer refuses two different things with one sentence each: a method whose code is
 * longer than 65535 bytes and one whose code is empty share a message, and a constant-pool index past
 * 65535 shares its message with an index of zero. Only one side of each pair is something the author
 * wrote too much of; the other is this compiler emitting nothing, or emitting a reference it never
 * pooled. Reading the number is what tells them apart, and what is not a limit stays an exception.
 */
class AClassfileRefusalIsALimitOnlyWhenTheNumberSaysSoTest {

    private static JvmLimits.Counted counted(String said) {
        return assertInstanceOf(JvmLimits.Counted.class,
                JvmLimits.exceeded(new IllegalArgumentException(said)));
    }

    @Test
    void codeLongerThanAMethodHoldsIsTheCodeSizeLimit() {
        JvmLimits.Counted e =
                counted("Code length 65539 is outside the allowed range in apply(Object)Object");

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
    void anIndexPastWhatAConstantPoolAddressesIsTheConstantPoolLimit() {
        JvmLimits.Counted e = counted("80031 is not a valid index. Entry: 11 java/util/List.copyOf-"
                + "(Ljava/util/Collection;)Ljava/util/List;");

        assertEquals(JvmLimits.Limit.CONSTANT_POOL_INDEX, e.limit());
        assertEquals(80031, e.measured());
        assertNull(e.method(), "the writer does not say which method it was writing");
    }

    @Test
    void aPoolWithMoreEntriesThanAClassFileHoldsIsTheConstantPoolLimitToo() {
        // the other refusal, from writing the pool out rather than from referring into it: the
        // number is how many entries there are, not which one was wanted
        JvmLimits.Counted e = counted("Constant pool is too large 70000");

        assertEquals(JvmLimits.Limit.CONSTANT_POOL_SIZE, e.limit());
        assertEquals(70000, e.measured());
    }

    @Test
    void anIndexBelowTheFirstEntryIsNotTheConstantPoolLimit() {
        assertNull(JvmLimits.exceeded(new IllegalArgumentException(
                "0 is not a valid index. Entry: 11 java/lang/Object")));
        assertNull(JvmLimits.exceeded(new IllegalArgumentException(
                "-1 is not a valid index. Entry: 11 java/lang/Object")));
    }

    @Test
    void theLastIndexAConstantPoolAddressesIsNotOverIt() {
        assertNull(JvmLimits.exceeded(new IllegalArgumentException(
                "65535 is not a valid index. Entry: 11 java/lang/Object")));
    }

    @Test
    void aPoolWithExactlyWhatAClassFileHoldsIsNotOverIt() {
        assertNull(JvmLimits.exceeded(
                new IllegalArgumentException("Constant pool is too large 65535")));
        assertEquals(JvmLimits.Limit.CONSTANT_POOL_SIZE,
                counted("Constant pool is too large 65536").limit());
    }

    @Test
    void theFirstIndexPastWhatAClassFileAddressesIsOverIt() {
        assertEquals(JvmLimits.Limit.CONSTANT_POOL_INDEX,
                counted("65536 is not a valid index. Entry: 11 java/lang/Object").limit());
    }

    /** A writer that measures a text as it pools it says how long it was. */
    @Test
    void aTextMeasuredAsItIsPooledIsTheTextLimit() {
        assertInstanceOf(JvmLimits.ATextTooLong.class, JvmLimits.exceeded(
                new IllegalArgumentException("utf8 length out of range of u2: 65536")));
        assertNull(JvmLimits.exceeded(
                new IllegalArgumentException("utf8 length out of range of u2: 65535")));
    }

    /** One that measures it only as it writes it out does not, and it is the same limit. */
    @Test
    void aTextMeasuredAsItIsWrittenIsTheTextLimitToo() {
        assertInstanceOf(JvmLimits.ATextTooLong.class, JvmLimits.exceeded(
                new IllegalArgumentException("string too long")));
    }

    /**
     * What the JDK running this says, asked of its own writer. Which of the two sentences it uses —
     * and so whether the tests above are about the writer at all — is this JDK's to answer.
     */
    @Test
    void theWriterThisRunsOnRefusesALongTextInASentenceReadAsTheTextLimit() {
        String longest = "a".repeat(65536);
        IllegalArgumentException refused = assertThrows(IllegalArgumentException.class,
                () -> ClassFile.of().build(ClassDesc.of("Probe"), cb -> cb.withMethodBody(
                        "text", MethodTypeDesc.of(ConstantDescs.CD_String), ClassFile.ACC_STATIC,
                        code -> code.ldc(longest).areturn())));

        assertInstanceOf(JvmLimits.ATextTooLong.class, JvmLimits.exceeded(refused),
                refused.getMessage());
    }

    @Test
    void anythingElseIsNotALimit() {
        assertNull(JvmLimits.exceeded(new IllegalArgumentException("bytecode offset out of range")));
        assertNull(JvmLimits.exceeded(new IllegalArgumentException()));
    }
}
