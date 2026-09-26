package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeElement;
import java.lang.classfile.CodeModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.InvokeInstruction;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * In the run time, a {@code java.math.BigDecimal} method that can refuse is called only at the
 * call sites below, each of which says why the refusal is reported or cannot happen there.
 *
 * <p>A {@code Decimal} is a {@code BigDecimal}, and most of what {@code BigDecimal} does can end
 * without an answer, in two ways. A sum, a product, a rescale or a stripped form can raise
 * {@code ArithmeticException} when {@code BigDecimal} cannot build the result it is asked for. A
 * product also derives its result's scale by adding its factors' scales, and that scale can itself
 * leave 32 bits, which a sum's, taken from the larger of its operands', cannot. And a plain notation
 * longer than a {@code String} raises an error. Where that reaches a program it reaches it as a
 * {@code java.math} exception from a program that has no such type, and not as the abort the
 * operation's contract names. The methods that
 * answer on every value — its sign, scale, precision and digits, a comparison, a negation — are not
 * a question here.
 *
 * <p>A row names the method making the call and the member it calls, by name and descriptor,
 * because the reason is that call's and not its class's: a class holding one call site whose
 * refusal cannot happen may still gain one whose refusal can.
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
     * The call sites that ask for something that can be refused.
     *
     * <p>Every {@code DecimalMath} row catches the refusal and reports it as the abort the operation
     * states, or — {@code plainText}, {@code ExactDecimals.leastDigits} — works out before the call
     * that it cannot
     * be refused: the text's length against what a {@code String} holds, and the zeros that can be
     * taken off before the scale reaches its floor. {@code multiply} also works out the product's
     * scale before the call, because {@code BigDecimal} answers some products whose scale is out of
     * range instead of refusing them. {@code ofDecimalText} is handed only text the
     * decimal-text grammar accepted, which has no exponent to overflow. {@code RationalMath.toInt}
     * reports the refusal itself. {@code Representations.canonicalNumber} rescales to zero only after
     * counting the digits that asks for and finding them few.
     */
    private static final List<String> MAY_BE_REFUSED = List.of(
            "souther/exact/ExactDecimals#leastDigits stripTrailingZeros()Ljava/math/BigDecimal;",
            "souther/runtime/DecimalMath#add add(Ljava/math/BigDecimal;)Ljava/math/BigDecimal;",
            "souther/runtime/DecimalMath#divide"
                    + " divide(Ljava/math/BigDecimal;ILjava/math/RoundingMode;)Ljava/math/BigDecimal;",
            "souther/runtime/DecimalMath#multiply multiply(Ljava/math/BigDecimal;)Ljava/math/BigDecimal;",
            "souther/runtime/DecimalMath#ofDecimalText <init>(Ljava/lang/String;)V",
            "souther/runtime/DecimalMath#plainText toPlainString()Ljava/lang/String;",
            "souther/runtime/DecimalMath#round setScale(ILjava/math/RoundingMode;)Ljava/math/BigDecimal;",
            "souther/runtime/DecimalMath#subtract subtract(Ljava/math/BigDecimal;)Ljava/math/BigDecimal;",
            "souther/runtime/DecimalMath#toInt longValueExact()J",
            "souther/runtime/DecimalMath#toInt setScale(ILjava/math/RoundingMode;)Ljava/math/BigDecimal;",
            "souther/runtime/RationalMath#toInt longValueExact()J",
            "souther/runtime/Representations#canonicalNumber setScale(I)Ljava/math/BigDecimal;");

    @Test
    void everyRunTimeCallThatCanBeRefusedIsWrittenDownHere() {
        assertEquals(MAY_BE_REFUSED, askingWhatCanBeRefused(),
                "a BigDecimal method that can refuse, called where nothing reports or rules out the"
                        + " refusal, leaks its java.math exception where the operation's contract"
                        + " names an abort");
    }

    /** And the walk sees a call at all, so an empty answer above would mean something. */
    @Test
    void theWalkFindsDecimalMath() {
        assertTrue(askingWhatCanBeRefused().stream()
                        .anyMatch(row -> row.startsWith("souther/runtime/DecimalMath#add ")),
                "every Decimal sum is in DecimalMath, so a walk not finding it is finding nothing");
    }

    private static List<String> askingWhatCanBeRefused() {
        Set<String> out = new TreeSet<>();
        for (ClassModel each : COMPILED.classesOf(COMPILED.module("souther-runtime"))) {
            for (MethodModel method : each.methods()) {
                for (CodeModel code : method.code().stream().toList()) {
                    for (CodeElement element : code) {
                        if (element instanceof InvokeInstruction invoke
                                && invoke.owner().asInternalName().equals(BIG_DECIMAL)) {
                            String member = invoke.name().stringValue() + invoke.type().stringValue();
                            if (!ANSWERS_ON_EVERY_VALUE.contains(member)) {
                                out.add(each.thisClass().asInternalName() + "#"
                                        + method.methodName().stringValue() + " " + member);
                            }
                        }
                    }
                }
            }
        }
        return new ArrayList<>(out);
    }
}
