package souther.architecture;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * In {@code souther-compiler}, a {@code java.math.BigDecimal} method that can refuse is called
 * only at the call sites below, each carrying why the refusal is reported or cannot happen there.
 *
 * <p>{@link BigDecimalCalls} walks the population and names each call by its caller and the member
 * it calls; the run time's own call sites are audited by
 * {@link WhoMayAskBigDecimalWhatItCanRefuseTest}, not this one, since a rule about this module and
 * a rule about {@code souther-runtime} are about two populations.
 *
 * <p><b>A reason per row, and not a string a developer can add without one.</b> A row is
 * {@link Reason#REFUSAL_TRANSLATED} where the call is inside a try/catch (or an equal guard stated
 * before the call) that turns the refusal into a meaning the caller's contract already names — an
 * {@code Optional.empty()}, a {@code null}, a {@code Cardinality.UNKNOWN}, or a documented exception
 * naming a broken internal invariant rather than the raw {@code java.math} one. A row is
 * {@link Reason#REFUSAL_IMPOSSIBLE} where a fact of the calling method's own body rules the refusal
 * out outright: a division whose divisor is never nought and whose operands' scales are both
 * bounded — a divisor that is never nought rules out only one of the two refusals a division has,
 * the other being the room the quotient's scale needs — a sum, difference or product whose
 * operands' scales and magnitudes the same method bounds, a value the same method has already
 * proven whole and in range. Both halves are needed. A sum is written at the finer of its two
 * scales, so a nought written to two billion places turns an addend of one into two billion
 * digits: that a result's scale is a valid {@code int} is no proof. And two operands at one scale
 * still add as two whole numbers, which the host holds only so many digits of: sharing a scale is
 * no proof either.
 *
 * <p><b>The proof is the method's, never its callers'.</b> The scanner sees the call site and
 * nothing that reaches it, so a proof leaning on what a caller passes, what a declaration table
 * allows or what another module's scanner emits is one a new caller makes false with this
 * population unchanged. Where a call has a precondition, the method checks it itself, or does the
 * arithmetic as numbers and has no such call. The one reach a row may make is into a private
 * helper of the same class, whose callers are all in the file.
 *
 * <p>{@link Permission#call()} alone is checked against the scanner's population; {@code reason}
 * and {@code why} are for a reader and for the next person to touch a row, not for the assertion —
 * a string list would have let either drift from what the code above it actually does.
 */
class WhoMayAskCompilerCallSitesWhatTheyCanRefuseTest {

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    /** Which of the two ways a row earns its place, said in the type and not left to a comment
     *  a reviewer has to take on faith. */
    private enum Reason {
        REFUSAL_TRANSLATED,
        REFUSAL_IMPOSSIBLE
    }

    /**
     * One call site this compiler allows to call a refusable {@code BigDecimal} member.
     *
     * @param call the caller and the member, exactly as {@link BigDecimalCalls.Call#row()} spells it
     * @param why  why {@code reason} holds here, specific to this call site. Never blank: a row
     *             carrying no more than its own {@code reason} is a claim nobody wrote the argument
     *             for
     */
    private record Permission(String call, Reason reason, String why) {

        Permission {
            java.util.Objects.requireNonNull(call, "a permission says which call it is of");
            java.util.Objects.requireNonNull(reason, "a permission says which of the two it is");
            if (why == null || why.isBlank()) {
                throw new IllegalArgumentException(
                        "a permission says why, and " + call + " does not");
            }
        }
    }

    private static final List<Permission> MAY_BE_REFUSED = List.of(
            new Permission(
                    "souther/compiler/check/Carrier#valueOf(Lsouther/compiler/numeric/Place;)"
                            + "Lsouther/compiler/observe/ObservedValue; longValueExact()J",
                    Reason.REFUSAL_IMPOSSIBLE,
                    "Reached through Carrier.requiredOnGrid, which throws unless onTheGrid already"
                            + " proved the place both whole and inside Whole's own extent — a range"
                            + " trivially inside long."),
            new Permission(
                    "souther/compiler/check/Carrier$Ordinal#caseAt(Lsouther/compiler/numeric/"
                            + "Place;)Lsouther/compiler/types/TypeSymbol; intValueExact()I",
                    Reason.REFUSAL_IMPOSSIBLE,
                    "Same choke point as Carrier#valueOf; Ordinal's own extent is 0..cases.size()-1,"
                            + " trivially inside int since cases is a List."),
            new Permission(
                    "souther/compiler/check/ConstantAlgebra#arith(Lsouther/compiler/types/BinOp;"
                            + "Ljava/lang/Object;Ljava/lang/Object;)Ljava/util/Optional;"
                            + " add(Ljava/math/BigDecimal;)Ljava/math/BigDecimal;",
                    Reason.REFUSAL_TRANSLATED,
                    "Inside try/catch(ArithmeticException) returning Optional.empty(), the fold's"
                            + " own documented answer for a sum this compiler could not compute."),
            new Permission(
                    "souther/compiler/check/ConstantAlgebra#arith(Lsouther/compiler/types/BinOp;"
                            + "Ljava/lang/Object;Ljava/lang/Object;)Ljava/util/Optional;"
                            + " multiply(Ljava/math/BigDecimal;)Ljava/math/BigDecimal;",
                    Reason.REFUSAL_TRANSLATED,
                    "Same try/catch as the add above, plus a pre-check on the product's own scale"
                            + " before the call; the catch covers what the pre-check leaves."),
            new Permission(
                    "souther/compiler/check/ConstantAlgebra#arith(Lsouther/compiler/types/BinOp;"
                            + "Ljava/lang/Object;Ljava/lang/Object;)Ljava/util/Optional;"
                            + " subtract(Ljava/math/BigDecimal;)Ljava/math/BigDecimal;",
                    Reason.REFUSAL_TRANSLATED,
                    "Same try/catch as the add above."),
            new Permission(
                    "souther/compiler/check/OccurrenceValues#wholeValuesAt(Lsouther/compiler/"
                            + "check/RuleKey;)Lsouther/compiler/check/Cardinality; longValueExact()J",
                    Reason.REFUSAL_TRANSLATED,
                    "try/catch(ArithmeticException) answers Cardinality.UNKNOWN, which is already"
                            + " this method's own answer for a span it cannot bound."),
            new Permission(
                    "souther/compiler/check/ScaleRange#receivedUnchanged(Ljava/math/BigDecimal;)"
                            + "Ljava/lang/Integer; intValueExact()I",
                    Reason.REFUSAL_TRANSLATED,
                    "try/catch(ArithmeticException) answers null, this method's own documented"
                            + " answer for a scale the run time could not be handed."),
            new Permission(
                    "souther/compiler/frontend/AstBuilder#decimalWritten(Ljava/lang/String;"
                            + "Lsouther/compiler/diag/SourcePos;)Ljava/math/BigDecimal;"
                            + " <init>(Ljava/lang/String;)V",
                    Reason.REFUSAL_TRANSLATED,
                    "The method checks the text is digits with at most one point between two runs"
                            + " of them, so its places fit an int scale; a text with more digits"
                            + " than a whole number the host holds is caught and reported as"
                            + " ADecimalLiteralHasMoreDigitsThanADecimalHolds."),
            new Permission(
                    "souther/compiler/inputs/Distinctions#whole(Ljava/math/BigDecimal;)Z"
                            + " longValueExact()J",
                    Reason.REFUSAL_TRANSLATED,
                    "try/catch(ArithmeticException) answers false, this predicate's own documented"
                            + " answer for a value that is not a whole number this host holds."),
            new Permission(
                    "souther/compiler/numeric/Dates#dateAt(Lsouther/compiler/numeric/Place;)"
                            + "Ljava/time/LocalDate; longValueExact()J",
                    Reason.REFUSAL_IMPOSSIBLE,
                    "The method refuses a count that is not whole or lies outside LocalDate's"
                            + " epoch days before this line, so the value is a whole number inside"
                            + " long, whatever scale it was written at."),
            new Permission(
                    "souther/compiler/numeric/Instants#countAt(Ljava/time/Instant;)Lsouther/"
                            + "compiler/numeric/Count; add(Ljava/math/BigDecimal;)Ljava/math/"
                            + "BigDecimal;",
                    Reason.REFUSAL_IMPOSSIBLE,
                    "Both operands are BigDecimal.valueOf(long/int) — always scale nought — so the"
                            + " sum needs no room past either side's own, already-valid scale."),
            new Permission(
                    "souther/compiler/numeric/Instants#countAt(Ljava/time/Instant;)Lsouther/"
                            + "compiler/numeric/Count; multiply(Ljava/math/BigDecimal;)Ljava/math/"
                            + "BigDecimal;",
                    Reason.REFUSAL_IMPOSSIBLE,
                    "Both factors scale nought (BigDecimal.valueOf(long) and a scale-nought"
                            + " constant); a product of two scale-nought values is scale nought."),
            new Permission(
                    "souther/compiler/observe/WaitShown#of(Ljava/time/Duration;)Ljava/lang/String;"
                            + " add(Ljava/math/BigDecimal;)Ljava/math/BigDecimal;",
                    Reason.REFUSAL_IMPOSSIBLE,
                    "Every operand's scale is fixed by Duration's own long/int fields (nought,"
                            + " nought, six) — a compile-time-bounded range, not merely a usual one."),
            new Permission(
                    "souther/compiler/observe/WaitShown#of(Ljava/time/Duration;)Ljava/lang/String;"
                            + " multiply(Ljava/math/BigDecimal;)Ljava/math/BigDecimal;",
                    Reason.REFUSAL_IMPOSSIBLE,
                    "Both factors scale nought, the same fixed-by-construction bound as the add"
                            + " above."),
            new Permission(
                    "souther/compiler/observe/WaitShown#of(Ljava/time/Duration;)Ljava/lang/String;"
                            + " stripTrailingZeros()Ljava/math/BigDecimal;",
                    Reason.REFUSAL_IMPOSSIBLE,
                    "Applied to a value whose scale is at most six by the construction above, far"
                            + " from the scale-overflow range this member's refusal needs."),
            new Permission(
                    "souther/compiler/observe/WaitShown#of(Ljava/time/Duration;)Ljava/lang/String;"
                            + " toPlainString()Ljava/lang/String;",
                    Reason.REFUSAL_IMPOSSIBLE,
                    "Same bounded-scale value; toPlainString has no documented throw for a value at"
                            + " an ordinary scale."),
            new Permission(
                    "souther/compiler/partition/FixtureTemplate#decimal(Ljava/math/BigDecimal;)"
                            + "Lsouther/compiler/partition/FixtureTemplate; toPlainString()Ljava/"
                            + "lang/String;",
                    Reason.REFUSAL_IMPOSSIBLE,
                    "Reached only after ExactDecimals.fitsPlainNotation returned true for the same"
                            + " value, on the line immediately above."),
            new Permission(
                    "souther/compiler/partition/FixtureTemplate#on(Lsouther/compiler/check/"
                            + "Carrier;Lsouther/compiler/numeric/Place;Lsouther/compiler/types/"
                            + "TypeReachName$Naming;)Lsouther/compiler/partition/FixtureTemplate;"
                            + " longValueExact()J",
                    Reason.REFUSAL_IMPOSSIBLE,
                    "Guarded by carrier.onTheGrid(at) == null returning null on the line just"
                            + " above; the call sits in the Whole arm, whose onTheGrid gate is the"
                            + " same choke point as Carrier#valueOf."),
            new Permission(
                    "souther/compiler/partition/LevelRealizer$Search#walking(ILsouther/compiler/"
                            + "partition/CandidateDomain$Walking;Lsouther/compiler/numeric/"
                            + "ExactRatio;Lsouther/compiler/numeric/ExactRatio;Lsouther/compiler/"
                            + "inputs/SearchRegion;)Lsouther/compiler/partition/LevelRealizer"
                            + "$Reached; setScale(I)Ljava/math/BigDecimal;",
                    Reason.REFUSAL_TRANSLATED,
                    "The align of first and by to one scale is wrapped in try/catch"
                            + "(ArithmeticException), falling back to walkingExactly — the same"
                            + " exact walk this compiler already answers soundly with."),
            new Permission(
                    "souther/compiler/partition/LevelRealizer$Search#walking(ILsouther/compiler/"
                            + "partition/CandidateDomain$Walking;Lsouther/compiler/numeric/"
                            + "ExactRatio;Lsouther/compiler/numeric/ExactRatio;Lsouther/compiler/"
                            + "inputs/SearchRegion;)Lsouther/compiler/partition/LevelRealizer"
                            + "$Reached; setScale(I)Ljava/math/BigDecimal; #2",
                    Reason.REFUSAL_TRANSLATED,
                    "The second setScale of the same aligning pair, caught by the same try/catch."),
            new Permission(
                    "souther/compiler/partition/LevelRealizer$Search#walkingAtOneScale(ILjava/"
                            + "math/BigDecimal;Ljava/math/BigDecimal;Ljava/math/BigDecimal;"
                            + "Lsouther/compiler/numeric/ExactRatio;Lsouther/compiler/numeric/"
                            + "ExactRatio;Lsouther/compiler/inputs/SearchRegion;)Lsouther/compiler/"
                            + "partition/LevelRealizer$Reached; add(Ljava/math/BigDecimal;)Ljava/"
                            + "math/BigDecimal;",
                    Reason.REFUSAL_TRANSLATED,
                    "first and by share a scale, so no step builds digits to align them; a step to"
                            + " a value with more digits than the host holds is caught and the run"
                            + " carried on in exact ratios from the value just tried, which records"
                            + " the value it could not hold. No step is taken past last."),
            new Permission(
                    "souther/compiler/partition/TermRealizations#atThoseParts(Ljava/util/Map;"
                            + "Lsouther/compiler/types/Type;Lsouther/compiler/check/Carrier;"
                            + "Lsouther/compiler/check/RuleReadingSource;)Lsouther/compiler/"
                            + "partition/TermRealizations$Realization; add(Ljava/math/BigDecimal;)"
                            + "Ljava/math/BigDecimal;",
                    Reason.REFUSAL_IMPOSSIBLE,
                    "seconds starts at BigDecimal.ZERO and admitted.get(0) comes from the private"
                            + " wholeNumbers over the window this method writes, 0 to many() - 1,"
                            + " built as new BigDecimal of a BigInteger — so every term is scale"
                            + " nought, each part at most 59 times at most 3600, and the sum at"
                            + " most 86399."),
            new Permission(
                    "souther/compiler/partition/TermRealizations#atThoseParts(Ljava/util/Map;"
                            + "Lsouther/compiler/types/Type;Lsouther/compiler/check/Carrier;"
                            + "Lsouther/compiler/check/RuleReadingSource;)Lsouther/compiler/"
                            + "partition/TermRealizations$Realization; multiply(Ljava/math/"
                            + "BigDecimal;)Ljava/math/BigDecimal;",
                    Reason.REFUSAL_IMPOSSIBLE,
                    "Both operands scale nought and small: a count from the window 0 to many() - 1"
                            + " this method writes, times a fixed enum constant"
                            + " (each.getKey().seconds())."),
            new Permission(
                    "souther/compiler/partition/TermRealizations#whole(Lsouther/compiler/numeric/"
                            + "Place;)I intValueExact()I",
                    Reason.REFUSAL_TRANSLATED,
                    "try/catch(ArithmeticException) rethrows as an IllegalStateException naming a"
                            + " broken internal contract — a whole-number search that produced a"
                            + " place that is not itself whole — rather than the raw java.math"
                            + " exception."),
            new Permission(
                    "souther/compiler/partition/ValueClasses#whole(Ljava/math/BigDecimal;)"
                            + "Lsouther/compiler/partition/FixtureTemplate; longValueExact()J",
                    Reason.REFUSAL_TRANSLATED,
                    "try/catch(ArithmeticException) answers null."),
            new Permission(
                    "souther/compiler/semantics/OperationFacts#minutesAcrossEveryDateTime()J"
                            + " divideToIntegralValue(Ljava/math/BigDecimal;)Ljava/math/BigDecimal;",
                    Reason.REFUSAL_IMPOSSIBLE,
                    "Both operands are fixed and scale nought: the dividend is DateTimes.MAX minus"
                            + " DateTimes.MIN, each Count.of(long) of LocalDateTime.MIN/MAX's epoch"
                            + " second, and the divisor is BigDecimal.valueOf(60). That rules out"
                            + " divideToIntegralValue's scale-difference refusal as well as its"
                            + " zero-divisor one — a non-zero divisor alone would rule out only the"
                            + " second."),
            new Permission(
                    "souther/compiler/semantics/OperationFacts#minutesAcrossEveryDateTime()J"
                            + " longValueExact()J",
                    Reason.REFUSAL_IMPOSSIBLE,
                    "Operates on (DateTimes.MAX - DateTimes.MIN) / 60: LocalDateTime.MIN/MAX's epoch"
                            + " seconds are about ±3.2e16, so the quotient is about 1.05e15 — well"
                            + " inside long."),
            new Permission(
                    "souther/compiler/semantics/OperationFacts#minutesAcrossEveryDateTime()J"
                            + " subtract(Ljava/math/BigDecimal;)Ljava/math/BigDecimal;",
                    Reason.REFUSAL_IMPOSSIBLE,
                    "DateTimes.MAX and DateTimes.MIN are both Count.of(long)-derived, scale nought;"
                            + " subtracting two scale-nought values needs no further room."));

    @Test
    void everyCompilerCallThatCanBeRefusedIsWrittenDownHere() {
        assertEquals(
                MAY_BE_REFUSED.stream().map(Permission::call).sorted().toList(),
                askingWhatCanBeRefused(),
                "a BigDecimal method that can refuse, called where nothing reports, translates, or"
                        + " rules out the refusal, leaks its java.math exception where the compiler"
                        + " has no vocabulary for it");
    }

    /** And the walk sees a call at all, so an empty answer above would mean something. */
    @Test
    void theWalkFindsConstantAlgebra() {
        assertTrue(askingWhatCanBeRefused().stream()
                        .anyMatch(row -> row.startsWith("souther/compiler/check/ConstantAlgebra#")),
                "constant folding always reaches an add, a subtract or a multiply, so a walk not"
                        + " finding it is finding nothing");
    }

    private static List<String> askingWhatCanBeRefused() {
        return BigDecimalCalls.in(COMPILED.classesOf(COMPILED.module("souther-compiler"))).stream()
                .map(BigDecimalCalls.Call::row)
                .sorted()
                .toList();
    }
}
