package souther.architecture;

import org.junit.jupiter.api.Test;

import java.util.List;

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
 * operation's contract names. The methods that answer on every value ({@link
 * BigDecimalCalls#ANSWERS_ON_EVERY_VALUE}) are not a question here.
 *
 * <p>{@link BigDecimalCalls} walks the population and names each call by its caller and the member
 * it calls; the compiler's own call sites are audited by a check of its own, not this one, since
 * a rule about what this repository publishes and a rule about a second module are about two
 * populations.
 */
class WhoMayAskBigDecimalWhatItCanRefuseTest {

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

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
     * counting the digits that asks for and finding them few. {@code ExactDecimals.spelledBounded}
     * counts the same way and calls {@code toPlainString} only where the count stays under the same
     * limit, and calls {@code toString} instead where it does not — total on every value regardless
     * ({@link BigDecimalCalls#ANSWERS_ON_EVERY_VALUE}), so there is nothing there to explain.
     */
    private static final List<String> MAY_BE_REFUSED = List.of(
            "souther/exact/ExactDecimals#leastDigits(Ljava/math/BigDecimal;)Ljava/math/BigDecimal;"
                    + " stripTrailingZeros()Ljava/math/BigDecimal;",
            "souther/exact/ExactDecimals#spelledBounded(Ljava/math/BigDecimal;)Ljava/lang/String;"
                    + " toPlainString()Ljava/lang/String;",
            "souther/runtime/DecimalMath#add(Ljava/math/BigDecimal;Ljava/math/BigDecimal;)"
                    + "Ljava/math/BigDecimal; add(Ljava/math/BigDecimal;)Ljava/math/BigDecimal;",
            "souther/runtime/DecimalMath#divide(Ljava/math/BigDecimal;Ljava/math/BigDecimal;JL"
                    + "souther/runtime/RoundingMode;)Ljava/lang/Object;"
                    + " divide(Ljava/math/BigDecimal;ILjava/math/RoundingMode;)Ljava/math/BigDecimal;",
            "souther/runtime/DecimalMath#multiply(Ljava/math/BigDecimal;Ljava/math/BigDecimal;)"
                    + "Ljava/math/BigDecimal; multiply(Ljava/math/BigDecimal;)Ljava/math/BigDecimal;",
            "souther/runtime/DecimalMath#ofDecimalText(Ljava/lang/String;)Ljava/math/BigDecimal;"
                    + " <init>(Ljava/lang/String;)V",
            "souther/runtime/DecimalMath#plainText(Ljava/math/BigDecimal;)Ljava/lang/String;"
                    + " toPlainString()Ljava/lang/String;",
            "souther/runtime/DecimalMath#round(JLsouther/runtime/RoundingMode;Ljava/math/BigDecimal;)"
                    + "Ljava/math/BigDecimal; setScale(ILjava/math/RoundingMode;)"
                    + "Ljava/math/BigDecimal;",
            "souther/runtime/DecimalMath#subtract(Ljava/math/BigDecimal;Ljava/math/BigDecimal;)"
                    + "Ljava/math/BigDecimal; subtract(Ljava/math/BigDecimal;)Ljava/math/BigDecimal;",
            "souther/runtime/DecimalMath#toInt(Lsouther/runtime/RoundingMode;Ljava/math/BigDecimal;)J"
                    + " longValueExact()J",
            "souther/runtime/DecimalMath#toInt(Lsouther/runtime/RoundingMode;Ljava/math/BigDecimal;)J"
                    + " setScale(ILjava/math/RoundingMode;)Ljava/math/BigDecimal;",
            "souther/runtime/RationalMath#toInt(Lsouther/runtime/RoundingMode;Lsouther/runtime/Rational;)J"
                    + " longValueExact()J",
            "souther/runtime/Representations#canonicalNumber(Ljava/math/BigDecimal;)"
                    + "Ljava/math/BigDecimal; setScale(I)Ljava/math/BigDecimal;");

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
                        .anyMatch(row -> row.startsWith("souther/runtime/DecimalMath#add(")),
                "every Decimal sum is in DecimalMath, so a walk not finding it is finding nothing");
    }

    private static List<String> askingWhatCanBeRefused() {
        return BigDecimalCalls.in(COMPILED.classesOf(COMPILED.module("souther-runtime"))).stream()
                .map(BigDecimalCalls.Call::row)
                .sorted()
                .toList();
    }
}
