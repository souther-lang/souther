package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.lang.classfile.constantpool.MethodRefEntry;
import java.lang.classfile.constantpool.PoolEntry;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * In the run time, a {@code java.math.BigDecimal} method that can refuse is called from
 * {@code DecimalMath} and from the few places below that say why the refusal cannot happen there.
 *
 * <p>A {@code Decimal} is a {@code BigDecimal}, and most of what {@code BigDecimal} does can end
 * without an answer: a sum, a product, a rescale or a stripped form whose scale leaves 32 bits
 * raises {@code ArithmeticException}, and a plain notation longer than a {@code String} raises an
 * error. Where that reaches a program it reaches it as a {@code java.math} exception from a program
 * that has no such type, and not as the abort the operation's contract names. {@code DecimalMath}
 * is the class that reports each of those as the abort; a call to the same method from anywhere
 * else is an operation whose refusal nobody reported. The methods that answer on every value — its
 * sign, scale, precision and digits, a comparison, a negation — are not a question here.
 */
class WhoMayAskBigDecimalWhatItCanRefuseTest {

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    private static final String BIG_DECIMAL = "java/math/BigDecimal";

    /** The members that answer on every {@code BigDecimal}, by name and descriptor. */
    private static final Set<String> ANSWERS_ON_EVERY_VALUE = Set.of(
            "compareTo(Ljava/math/BigDecimal;)I",
            "equals(Ljava/lang/Object;)Z",
            "hashCode()I",
            "signum()I",
            "scale()I",
            "precision()I",
            "unscaledValue()Ljava/math/BigInteger;",
            "negate()Ljava/math/BigDecimal;",
            "valueOf(J)Ljava/math/BigDecimal;",
            "valueOf(JI)Ljava/math/BigDecimal;",
            "<init>(Ljava/math/BigInteger;)V",
            "<init>(Ljava/math/BigInteger;I)V");

    /**
     * The run-time classes that call a member that can refuse.
     *
     * <p>{@code DecimalMath} reports every refusal as an abort. {@code RationalMath} reads a whole
     * number out with {@code longValueExact} only after checking it is within {@code Int}, or where
     * it reports the refusal itself. {@code Representations} rescales an amount to zero only when it
     * has counted the digits that asks for and found them few.
     */
    private static final List<String> MAY_BE_REFUSED = List.of(
            "souther/runtime/DecimalMath",
            "souther/runtime/RationalMath",
            "souther/runtime/Representations");

    @Test
    void everyRunTimeClassThatCanBeRefusedIsWrittenDownHere() {
        assertEquals(MAY_BE_REFUSED, askingWhatCanBeRefused(),
                "a BigDecimal method that can refuse, called outside DecimalMath, leaks its"
                        + " java.math exception where the operation's contract names an abort");
    }

    /** And the walk sees a caller at all, so an empty answer above would mean something. */
    @Test
    void theWalkFindsDecimalMath() {
        assertTrue(askingWhatCanBeRefused().contains("souther/runtime/DecimalMath"),
                "every Decimal operation is in DecimalMath, so a walk not finding it is finding"
                        + " nothing");
    }

    private static List<String> askingWhatCanBeRefused() {
        Set<String> out = new TreeSet<>();
        for (ClassModel each : COMPILED.classesOf(COMPILED.module("souther-runtime"))) {
            for (PoolEntry entry : each.constantPool()) {
                if (entry instanceof MethodRefEntry method
                        && method.owner().name().stringValue().equals(BIG_DECIMAL)
                        && !ANSWERS_ON_EVERY_VALUE.contains(
                                method.name().stringValue() + method.type().stringValue())) {
                    out.add(each.thisClass().asInternalName());
                }
            }
        }
        return new ArrayList<>(out);
    }
}
