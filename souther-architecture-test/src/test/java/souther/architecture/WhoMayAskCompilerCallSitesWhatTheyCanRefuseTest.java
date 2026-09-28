package souther.architecture;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * In {@code souther-compiler}, a {@code java.math.BigDecimal} method that can refuse is called
 * only at the call sites below, each of which says why the refusal is reported or cannot happen
 * there.
 *
 * <p>{@link BigDecimalCalls} walks the population and names each call by its caller and the member
 * it calls; the run time's own call sites are audited by
 * {@link WhoMayAskBigDecimalWhatItCanRefuseTest}, not this one, since a rule about this module and
 * a rule about {@code souther-runtime} are about two populations.
 *
 * <p><b>Two ways a row here earns its place.</b> A row is translated where the call is inside a
 * try/catch (or an equal guard stated before the call) that turns the refusal into a meaning the
 * caller's own contract already names — an {@code Optional.empty()}, a {@code null}, a
 * {@code Cardinality.UNKNOWN}, or a documented exception naming a broken internal invariant rather
 * than the raw {@code java.math} one. A row is impossible where a local fact rules the refusal out
 * outright: a fixed divisor that is never nought, two operands proven to share one scale, a value
 * already proven whole and in range by a choke point the same file enforces. Where the proof holds
 * only because of what one particular caller happens to pass — {@link
 * souther.compiler.numeric.Dates#dateAt}, {@link souther.compiler.frontend.AstBuilder}'s decimal
 * literal — the row says so, naming the caller the proof leans on.
 */
class WhoMayAskCompilerCallSitesWhatTheyCanRefuseTest {

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    /**
     * The call sites that ask for something that can be refused.
     *
     * <p>{@code Carrier#valueOf}'s {@code Whole} arm, {@code Carrier$Ordinal#caseAt}, and
     * {@code FixtureTemplate#on}'s {@code Whole} arm all read through {@code Carrier.requiredOnGrid},
     * which throws unless {@code onTheGrid} has already proven the place both whole and inside the
     * carrier's own extent — a range trivially inside {@code long} or {@code int} for every carrier
     * that gate covers. {@code ConstantAlgebra#arith}, {@code OccurrenceValues#wholeValuesAt},
     * {@code ScaleRange#receivedUnchanged}, {@code Distinctions#whole}, and
     * {@code ValueClasses#whole} each catch the refusal and answer with a sentinel their own
     * signature already carries — {@code Optional.empty()}, {@code Cardinality.UNKNOWN}, or
     * {@code null}. {@code TermRealizations#whole} and
     * {@code Arithmetic$ATruncatingQuotient#quotientOf} translate it instead into a documented
     * exception naming the broken invariant, since neither has a value to fall back to.
     *
     * <p>{@code AstBuilder$Reading#literal} builds a {@code BigDecimal} from text the lexer accepts
     * only where it matches the decimal-literal grammar — a fact about {@code souther-syntax} and
     * not about this file, so the proof leans on that module's contract rather than standing on its
     * own. {@code Dates#dateAt} has no guard of its own either: its one caller,
     * {@code TermReading#partOfDate}, checks {@code observed.onTheGrid(count) != null} first, which
     * is where the wholeness and the range this needs are actually proven.
     *
     * <p>{@code TermReading#partOfTime}'s divisor is one of {@code TakenAs.TimePart}'s fixed
     * constants, never nought. {@code Count#plus} adds a whole-number step of scale nought to a
     * count of any scale, and a sum with one side at scale nought can never leave the range a scale
     * holds regardless of the other side's own. {@code Instants#countAt}'s two operands are both
     * built by {@code BigDecimal.valueOf} on a {@code long} or an {@code int}, so both sit at scale
     * nought. {@code Intervals$End#over} divides only past two branches that already return where
     * the divisor is nought or the quotient is settled otherwise. {@code WaitShown#of} builds every
     * operand at a scale fixed by {@code Duration}'s own primitive fields — nought, nought, or six —
     * nowhere near where a sum or a product of scales could run out of the range a scale holds.
     *
     * <p>{@code CandidateDomain#stepsTo} divides by {@code AffinePreimage.Stepping}'s {@code by},
     * always positive, at a scale of nought that a whole-number division never needs more room for;
     * its {@code add} closes the same whole-number result with a constant of that scale.
     * {@code ContainersAddingUp#shared}'s divisor is {@code many - i} inside a loop this file bounds
     * to never reach nought. {@code CutPosition#justBeyond} adds or subtracts a rounded line and a
     * step built to the same number of places as that rounding, so the two share one scale
     * whatever it is; moving a scale-nought {@code ONE} to any number of places never needs more
     * room than the place count itself already fits. {@code FixtureTemplate#decimal} only reaches
     * {@code toPlainString} once {@code ExactDecimals.fitsPlainNotation} has said the value is one
     * plain notation holds.
     *
     * <p>{@code TermRealizations#atThoseParts} adds and multiplies values {@code wholeNumbers}
     * builds at scale nought with a fixed enum constant, also scale nought.
     * {@code TermRealizations#endOf} and {@code #startOf} read their edge through
     * {@code ExactRatio.floor}/{@code ceiling} rather than {@code setScale}, so the only
     * {@code BigDecimal} arithmetic left is a scale-nought edge plus or minus a scale-nought
     * {@code ONE}; {@code #wholeNumbers} steps that same scale-nought result by that same constant.
     * {@code OperationFacts#minutesAcrossEveryDateTime} divides and reads back a difference of two
     * fixed {@code DateTimes} constants a JDK epoch-second range away from overflowing anything —
     * every number in it is fixed at compile time and inspectable by hand.
     */
    private static final List<String> MAY_BE_REFUSED = List.of(
            "souther/compiler/check/Carrier#valueOf(Lsouther/compiler/numeric/Place;)Lsouther/"
                    + "compiler/observe/ObservedValue; longValueExact()J",
            "souther/compiler/check/Carrier$Ordinal#caseAt(Lsouther/compiler/numeric/Place;)"
                    + "Lsouther/compiler/types/TypeSymbol; intValueExact()I",
            "souther/compiler/check/ConstantAlgebra#arith(Lsouther/compiler/types/BinOp;Ljava/lang"
                    + "/Object;Ljava/lang/Object;)Ljava/util/Optional; add(Ljava/math/BigDecimal;)"
                    + "Ljava/math/BigDecimal;",
            "souther/compiler/check/ConstantAlgebra#arith(Lsouther/compiler/types/BinOp;Ljava/lang"
                    + "/Object;Ljava/lang/Object;)Ljava/util/Optional; multiply(Ljava/math/"
                    + "BigDecimal;)Ljava/math/BigDecimal;",
            "souther/compiler/check/ConstantAlgebra#arith(Lsouther/compiler/types/BinOp;Ljava/lang"
                    + "/Object;Ljava/lang/Object;)Ljava/util/Optional; subtract(Ljava/math/"
                    + "BigDecimal;)Ljava/math/BigDecimal;",
            "souther/compiler/check/OccurrenceValues#wholeValuesAt(Lsouther/compiler/check/"
                    + "RuleKey;)Lsouther/compiler/check/Cardinality; longValueExact()J",
            "souther/compiler/check/ScaleRange#receivedUnchanged(Ljava/math/BigDecimal;)Ljava/"
                    + "lang/Integer; intValueExact()I",
            "souther/compiler/frontend/AstBuilder$Reading#literal(Lsouther/compiler/cst/"
                    + "SyntaxNode;)Lsouther/compiler/ast/Ast$Expr; <init>(Ljava/lang/String;)V",
            "souther/compiler/inputs/Distinctions#whole(Ljava/math/BigDecimal;)Z longValueExact()J",
            "souther/compiler/inputs/TermReading#partOfTime(Lsouther/compiler/semantics/TakenAs"
                    + "$TimePart;Lsouther/compiler/observe/ObservedValue;Lsouther/compiler/check/"
                    + "Carrier;)Lsouther/compiler/inputs/NumericTerm$Reading; "
                    + "divideToIntegralValue(Ljava/math/BigDecimal;)Ljava/math/BigDecimal;",
            "souther/compiler/inputs/TermReading#partOfTime(Lsouther/compiler/semantics/TakenAs"
                    + "$TimePart;Lsouther/compiler/observe/ObservedValue;Lsouther/compiler/check/"
                    + "Carrier;)Lsouther/compiler/inputs/NumericTerm$Reading; "
                    + "remainder(Ljava/math/BigDecimal;)Ljava/math/BigDecimal;",
            "souther/compiler/numeric/Count#plus(J)Lsouther/compiler/numeric/Count; add(Ljava/"
                    + "math/BigDecimal;)Ljava/math/BigDecimal;",
            "souther/compiler/numeric/Dates#dateAt(Lsouther/compiler/numeric/Place;)Ljava/time/"
                    + "LocalDate; longValueExact()J",
            "souther/compiler/numeric/Instants#countAt(Ljava/time/Instant;)Lsouther/compiler/"
                    + "numeric/Count; add(Ljava/math/BigDecimal;)Ljava/math/BigDecimal;",
            "souther/compiler/numeric/Instants#countAt(Ljava/time/Instant;)Lsouther/compiler/"
                    + "numeric/Count; multiply(Ljava/math/BigDecimal;)Ljava/math/BigDecimal;",
            "souther/compiler/numeric/Intervals$End#over(Lsouther/compiler/numeric/Intervals$End;"
                    + "IILjava/math/RoundingMode;)Lsouther/compiler/numeric/Intervals$Ratio; "
                    + "divide(Ljava/math/BigDecimal;ILjava/math/RoundingMode;)Ljava/math/"
                    + "BigDecimal;",
            "souther/compiler/observe/WaitShown#of(Ljava/time/Duration;)Ljava/lang/String; "
                    + "add(Ljava/math/BigDecimal;)Ljava/math/BigDecimal;",
            "souther/compiler/observe/WaitShown#of(Ljava/time/Duration;)Ljava/lang/String; "
                    + "multiply(Ljava/math/BigDecimal;)Ljava/math/BigDecimal;",
            "souther/compiler/observe/WaitShown#of(Ljava/time/Duration;)Ljava/lang/String; "
                    + "stripTrailingZeros()Ljava/math/BigDecimal;",
            "souther/compiler/observe/WaitShown#of(Ljava/time/Duration;)Ljava/lang/String; "
                    + "toPlainString()Ljava/lang/String;",
            "souther/compiler/partition/CandidateDomain#stepsTo(Lsouther/compiler/numeric/"
                    + "Endpoint;Lsouther/compiler/numeric/ExactRatio;Lsouther/compiler/numeric/"
                    + "ExactRatio;Z)Lsouther/compiler/partition/CandidateDomain$Multiplied; "
                    + "add(Ljava/math/BigDecimal;)Ljava/math/BigDecimal;",
            "souther/compiler/partition/CandidateDomain#stepsTo(Lsouther/compiler/numeric/"
                    + "Endpoint;Lsouther/compiler/numeric/ExactRatio;Lsouther/compiler/numeric/"
                    + "ExactRatio;Z)Lsouther/compiler/partition/CandidateDomain$Multiplied; "
                    + "divide(Ljava/math/BigDecimal;ILjava/math/RoundingMode;)Ljava/math/"
                    + "BigDecimal;",
            "souther/compiler/partition/ContainersAddingUp#shared(Ljava/math/BigDecimal;ILsouther"
                    + "/compiler/check/Carrier;)Ljava/math/BigDecimal; divide(Ljava/math/"
                    + "BigDecimal;ILjava/math/RoundingMode;)Ljava/math/BigDecimal;",
            "souther/compiler/partition/ContainersAddingUp#shared(Ljava/math/BigDecimal;ILsouther"
                    + "/compiler/check/Carrier;)Ljava/math/BigDecimal; divideToIntegralValue(Ljava"
                    + "/math/BigDecimal;)Ljava/math/BigDecimal;",
            "souther/compiler/partition/CutPosition#justBeyond(Lsouther/compiler/numeric/Towards;"
                    + "I)Lsouther/compiler/partition/CutPosition$JustBeyond; add(Ljava/math/"
                    + "BigDecimal;)Ljava/math/BigDecimal;",
            "souther/compiler/partition/CutPosition#justBeyond(Lsouther/compiler/numeric/Towards;"
                    + "I)Lsouther/compiler/partition/CutPosition$JustBeyond; "
                    + "movePointLeft(I)Ljava/math/BigDecimal;",
            "souther/compiler/partition/CutPosition#justBeyond(Lsouther/compiler/numeric/Towards;"
                    + "I)Lsouther/compiler/partition/CutPosition$JustBeyond; subtract(Ljava/math/"
                    + "BigDecimal;)Ljava/math/BigDecimal;",
            "souther/compiler/partition/FixtureTemplate#decimal(Ljava/math/BigDecimal;)Lsouther/"
                    + "compiler/partition/FixtureTemplate; toPlainString()Ljava/lang/String;",
            "souther/compiler/partition/FixtureTemplate#on(Lsouther/compiler/check/Carrier;"
                    + "Lsouther/compiler/numeric/Place;Lsouther/compiler/types/TypeReachName"
                    + "$Naming;)Lsouther/compiler/partition/FixtureTemplate; longValueExact()J",
            "souther/compiler/partition/TermRealizations#atThoseParts(Ljava/util/Map;Lsouther/"
                    + "compiler/types/Type;Lsouther/compiler/check/Carrier;Lsouther/compiler/"
                    + "check/RuleReadingSource;)Lsouther/compiler/partition/TermRealizations"
                    + "$Realization; add(Ljava/math/BigDecimal;)Ljava/math/BigDecimal;",
            "souther/compiler/partition/TermRealizations#atThoseParts(Ljava/util/Map;Lsouther/"
                    + "compiler/types/Type;Lsouther/compiler/check/Carrier;Lsouther/compiler/"
                    + "check/RuleReadingSource;)Lsouther/compiler/partition/TermRealizations"
                    + "$Realization; multiply(Ljava/math/BigDecimal;)Ljava/math/BigDecimal;",
            "souther/compiler/partition/TermRealizations#endOf(Lsouther/compiler/numeric/"
                    + "Endpoint;Ljava/math/BigDecimal;)Ljava/math/BigDecimal; subtract(Ljava/math"
                    + "/BigDecimal;)Ljava/math/BigDecimal;",
            "souther/compiler/partition/TermRealizations#startOf(Lsouther/compiler/numeric/"
                    + "Endpoint;Ljava/math/BigDecimal;)Ljava/math/BigDecimal; add(Ljava/math/"
                    + "BigDecimal;)Ljava/math/BigDecimal;",
            "souther/compiler/partition/TermRealizations#whole(Lsouther/compiler/numeric/Place;)I"
                    + " intValueExact()I",
            "souther/compiler/partition/TermRealizations#wholeNumbers(Lsouther/compiler/numeric/"
                    + "NumericDomain$Bounds;Ljava/util/function/Predicate;Ljava/math/BigDecimal;"
                    + "Ljava/math/BigDecimal;I)Lsouther/compiler/partition/TermRealizations$Tried;"
                    + " add(Ljava/math/BigDecimal;)Ljava/math/BigDecimal;",
            "souther/compiler/partition/ValueClasses#whole(Ljava/math/BigDecimal;)Lsouther/"
                    + "compiler/partition/FixtureTemplate; longValueExact()J",
            "souther/compiler/semantics/Arithmetic$ATruncatingQuotient#quotientOf(Ljava/math/"
                    + "BigDecimal;Ljava/math/BigDecimal;)Ljava/math/BigDecimal; "
                    + "divideToIntegralValue(Ljava/math/BigDecimal;)Ljava/math/BigDecimal;",
            "souther/compiler/semantics/OperationFacts#minutesAcrossEveryDateTime()J "
                    + "divideToIntegralValue(Ljava/math/BigDecimal;)Ljava/math/BigDecimal;",
            "souther/compiler/semantics/OperationFacts#minutesAcrossEveryDateTime()J "
                    + "longValueExact()J",
            "souther/compiler/semantics/OperationFacts#minutesAcrossEveryDateTime()J "
                    + "subtract(Ljava/math/BigDecimal;)Ljava/math/BigDecimal;");

    @Test
    void everyCompilerCallThatCanBeRefusedIsWrittenDownHere() {
        assertEquals(MAY_BE_REFUSED, askingWhatCanBeRefused(),
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
