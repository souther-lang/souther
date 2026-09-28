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
 * {@link Reason#REFUSAL_IMPOSSIBLE} where a local fact rules the refusal out outright: a fixed
 * divisor that is never nought, two operands proven to share one scale, a value already proven
 * whole and in range by a choke point the same file enforces. Where the proof holds only because of
 * what one particular caller happens to pass — {@link souther.compiler.numeric.Dates#dateAt},
 * {@link souther.compiler.frontend.AstBuilder}'s decimal literal — the row's {@code why} says so,
 * naming the caller the proof leans on. {@link Permission#call()} alone is checked against the
 * scanner's population; {@code reason} and {@code why} are for a reader and for the next person to
 * touch a row, not for the assertion — a string list would have let either drift from what the code
 * above it actually does, which is what named the misreading {@link Permission#call()} corrects
 * for {@code Arithmetic$ATruncatingQuotient#quotientOf}, below.
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
                    "souther/compiler/frontend/AstBuilder$Reading#literal(Lsouther/compiler/cst/"
                            + "SyntaxNode;)Lsouther/compiler/ast/Ast$Expr; <init>(Ljava/lang/"
                            + "String;)V",
                    Reason.REFUSAL_IMPOSSIBLE,
                    "Single-caller-dependent on souther-syntax's own lexer grammar: a DECIMAL_LIT"
                            + " token only ever matches digits(.digits)?, optionally suffixed m,"
                            + " which stripDecimalSuffix leaves as exactly what BigDecimal(String)"
                            + " always parses. Not provable from this file alone."),
            new Permission(
                    "souther/compiler/inputs/Distinctions#whole(Ljava/math/BigDecimal;)Z"
                            + " longValueExact()J",
                    Reason.REFUSAL_TRANSLATED,
                    "try/catch(ArithmeticException) answers false, this predicate's own documented"
                            + " answer for a value that is not a whole number this host holds."),
            new Permission(
                    "souther/compiler/inputs/TermReading#partOfTime(Lsouther/compiler/semantics/"
                            + "TakenAs$TimePart;Lsouther/compiler/observe/ObservedValue;Lsouther/"
                            + "compiler/check/Carrier;)Lsouther/compiler/inputs/NumericTerm"
                            + "$Reading; divideToIntegralValue(Ljava/math/BigDecimal;)Ljava/math/"
                            + "BigDecimal;",
                    Reason.REFUSAL_IMPOSSIBLE,
                    "TakenAs.PartOfTime is only ever declared for Time's own operations"
                            + " (OperationFacts: Time.hour/minute/second), so the dividend is a"
                            + " Times-carrier count — scale 0, bounded 0..86399 by Times.MIN/MAX —"
                            + " and the divisor is a fixed positive TimePart constant (3600/60/1)."
                            + " divideToIntegralValue's own scale-difference bound, not only a"
                            + " non-zero divisor, is what this rules out."),
            new Permission(
                    "souther/compiler/inputs/TermReading#partOfTime(Lsouther/compiler/semantics/"
                            + "TakenAs$TimePart;Lsouther/compiler/observe/ObservedValue;Lsouther/"
                            + "compiler/check/Carrier;)Lsouther/compiler/inputs/NumericTerm"
                            + "$Reading; remainder(Ljava/math/BigDecimal;)Ljava/math/BigDecimal;",
                    Reason.REFUSAL_IMPOSSIBLE,
                    "Same Times-bounded dividend as the divideToIntegralValue above, same fixed"
                            + " positive divisor family (part.many())."),
            new Permission(
                    "souther/compiler/numeric/Count#plus(J)Lsouther/compiler/numeric/Count;"
                            + " add(Ljava/math/BigDecimal;)Ljava/math/BigDecimal;",
                    Reason.REFUSAL_IMPOSSIBLE,
                    "at.add(BigDecimal.valueOf(steps)): the addend is always scale nought, and a sum"
                            + " with one side at scale nought needs no room past what the other"
                            + " side's own scale — already a valid int — already fits, whatever that"
                            + " scale is."),
            new Permission(
                    "souther/compiler/numeric/Dates#dateAt(Lsouther/compiler/numeric/Place;)"
                            + "Ljava/time/LocalDate; longValueExact()J",
                    Reason.REFUSAL_IMPOSSIBLE,
                    "Single-caller-dependent: no local guard here, but the one caller outside"
                            + " Carrier, TermReading#partOfDate, checks observed.onTheGrid(count)"
                            + " != null first, which proves Days' own wholeness and extent before"
                            + " this runs."),
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
                    "souther/compiler/partition/CutPosition#justBeyond(Lsouther/compiler/numeric/"
                            + "Towards;I)Lsouther/compiler/partition/CutPosition$JustBeyond;"
                            + " add(Ljava/math/BigDecimal;)Ljava/math/BigDecimal;",
                    Reason.REFUSAL_IMPOSSIBLE,
                    "past comes from ExactRatio#asDecimal rounded to exactly digits places, and"
                            + " step is ONE.movePointLeft(digits) — both share that same scale, so"
                            + " the sum needs no room past a scale it already has, whatever it is."),
            new Permission(
                    "souther/compiler/partition/CutPosition#justBeyond(Lsouther/compiler/numeric/"
                            + "Towards;I)Lsouther/compiler/partition/CutPosition$JustBeyond;"
                            + " movePointLeft(I)Ljava/math/BigDecimal;",
                    Reason.REFUSAL_IMPOSSIBLE,
                    "ONE has scale nought, so moving it to scale digits needs digits itself to be a"
                            + " valid int — which it already is, being one — for any sign of it."),
            new Permission(
                    "souther/compiler/partition/CutPosition#justBeyond(Lsouther/compiler/numeric/"
                            + "Towards;I)Lsouther/compiler/partition/CutPosition$JustBeyond;"
                            + " subtract(Ljava/math/BigDecimal;)Ljava/math/BigDecimal;",
                    Reason.REFUSAL_IMPOSSIBLE,
                    "Same equal-scale reasoning as the add above."),
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
                    Reason.REFUSAL_IMPOSSIBLE,
                    "first and by were aligned to one scale immediately before this loop runs, and"
                            + " a same-scale sum can never leave the range a scale holds, whatever"
                            + " that scale turned out to be."),
            new Permission(
                    "souther/compiler/partition/TermRealizations#atThoseParts(Ljava/util/Map;"
                            + "Lsouther/compiler/types/Type;Lsouther/compiler/check/Carrier;"
                            + "Lsouther/compiler/check/RuleReadingSource;)Lsouther/compiler/"
                            + "partition/TermRealizations$Realization; add(Ljava/math/BigDecimal;)"
                            + "Ljava/math/BigDecimal;",
                    Reason.REFUSAL_IMPOSSIBLE,
                    "seconds starts at BigDecimal.ZERO and admitted.get(0) comes from wholeNumbers,"
                            + " whose candidates are always scale nought — so this add is always"
                            + " scale-nought-plus-scale-nought."),
            new Permission(
                    "souther/compiler/partition/TermRealizations#atThoseParts(Ljava/util/Map;"
                            + "Lsouther/compiler/types/Type;Lsouther/compiler/check/Carrier;"
                            + "Lsouther/compiler/check/RuleReadingSource;)Lsouther/compiler/"
                            + "partition/TermRealizations$Realization; multiply(Ljava/math/"
                            + "BigDecimal;)Ljava/math/BigDecimal;",
                    Reason.REFUSAL_IMPOSSIBLE,
                    "Both operands scale nought: a whole-number count times a fixed enum constant"
                            + " (each.getKey().seconds())."),
            new Permission(
                    "souther/compiler/partition/TermRealizations#endOf(Lsouther/compiler/numeric/"
                            + "Endpoint;Ljava/math/BigDecimal;)Ljava/math/BigDecimal;"
                            + " subtract(Ljava/math/BigDecimal;)Ljava/math/BigDecimal;",
                    Reason.REFUSAL_IMPOSSIBLE,
                    "edge comes from ExactRatio#floor, always a whole number (scale nought), minus"
                            + " a scale-nought ONE."),
            new Permission(
                    "souther/compiler/partition/TermRealizations#startOf(Lsouther/compiler/"
                            + "numeric/Endpoint;Ljava/math/BigDecimal;)Ljava/math/BigDecimal;"
                            + " add(Ljava/math/BigDecimal;)Ljava/math/BigDecimal;",
                    Reason.REFUSAL_IMPOSSIBLE,
                    "Mirror of endOf above: edge from ExactRatio#ceiling, scale nought, plus a"
                            + " scale-nought ONE."),
            new Permission(
                    "souther/compiler/partition/TermRealizations#whole(Lsouther/compiler/numeric/"
                            + "Place;)I intValueExact()I",
                    Reason.REFUSAL_TRANSLATED,
                    "try/catch(ArithmeticException) rethrows as an IllegalStateException naming a"
                            + " broken internal contract — a whole-number search that produced a"
                            + " place that is not itself whole — rather than the raw java.math"
                            + " exception."),
            new Permission(
                    "souther/compiler/partition/TermRealizations#wholeNumbers(Lsouther/compiler/"
                            + "numeric/NumericDomain$Bounds;Ljava/util/function/Predicate;Ljava/"
                            + "math/BigDecimal;Ljava/math/BigDecimal;I)Lsouther/compiler/partition/"
                            + "TermRealizations$Tried; add(Ljava/math/BigDecimal;)Ljava/math/"
                            + "BigDecimal;",
                    Reason.REFUSAL_IMPOSSIBLE,
                    "The accumulator starts at startOf/endOf's own scale-nought result and steps by"
                            + " a scale-nought ONE every iteration, so the scale never moves."),
            new Permission(
                    "souther/compiler/partition/ValueClasses#whole(Ljava/math/BigDecimal;)"
                            + "Lsouther/compiler/partition/FixtureTemplate; longValueExact()J",
                    Reason.REFUSAL_TRANSLATED,
                    "try/catch(ArithmeticException) answers null."),
            new Permission(
                    "souther/compiler/semantics/Arithmetic$ATruncatingQuotient#quotientOf(Ljava/"
                            + "math/BigDecimal;Ljava/math/BigDecimal;)Ljava/math/BigDecimal;"
                            + " divideToIntegralValue(Ljava/math/BigDecimal;)Ljava/math/BigDecimal;",
                    Reason.REFUSAL_IMPOSSIBLE,
                    "by.signum() == 0 returns before this line, throwing its own"
                            + " IllegalArgumentException early rather than catching this member's"
                            + " own exception — so the actual call is guarded by a precondition, not"
                            + " a translation around it. That guard alone rules out only one of"
                            + " divideToIntegralValue's two throw conditions; the other is ruled out"
                            + " by TakenAs.TheTruncatingQuotient.takenOf() only ever taking Int -> Int,"
                            + " so both operands are scale-0, long-range-bounded Int values."),
            new Permission(
                    "souther/compiler/semantics/OperationFacts#minutesAcrossEveryDateTime()J"
                            + " divideToIntegralValue(Ljava/math/BigDecimal;)Ljava/math/BigDecimal;",
                    Reason.REFUSAL_IMPOSSIBLE,
                    "Divisor is the literal constant BigDecimal.valueOf(60), never nought."),
            new Permission(
                    "souther/compiler/semantics/OperationFacts#minutesAcrossEveryDateTime()J"
                            + " longValueExact()J",
                    Reason.REFUSAL_IMPOSSIBLE,
                    "Operates on (DateTimes.MAX - DateTimes.MIN) / 60, fixed compile-time JDK"
                            + " epoch-second constants roughly ±5e15 apart — well inside long."),
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
