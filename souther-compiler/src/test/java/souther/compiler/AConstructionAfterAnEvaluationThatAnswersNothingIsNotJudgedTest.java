package souther.compiler;

import souther.compiler.diag.Diagnostic;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * An evaluation no run carries a value on from is one nothing is written after.
 *
 * <p>A primitive is defined on some of what its type admits and not on the rest: {@code Int.divide}
 * answers no number for the one pair whose quotient no {@code Int} holds, and aborts (spec
 * §stdlib-int). Where the operands here are only such pairs, every run that reaches the operation
 * stops at it — so a construction written below it is one no run reaches, and judging it answers a
 * question about reachability with a reading of the values (#980).
 *
 * <p><b>Three questions and not one.</b> Whether the arithmetic produced a number is asked of the
 * recipe; whether the operation answered at all takes its other cases in as well, since a divide by
 * zero comes back as a case and an arm is reached there; and whether a place is reached is about the
 * continuation. Run together, they answer each other: a value case with no number in it is not an
 * operation that aborts, and an operation that aborts is not a clause the value fails.
 *
 * <p><b>Not-known-to-abort is not unreachable.</b> Every row below where the operands admit one pair
 * the operation answers is a row where nothing changes, and that is the direction this reading takes
 * everywhere — an operation this cannot name, an operand nothing bounds, a case it cannot rule out.
 *
 * <p><b>What runs before the abort still runs.</b> A construction among the values an aborting
 * evaluation is waiting on is one the program really builds, and it is judged. That is the whole
 * difference between an evaluation nothing leaves and a place nothing arrives at.
 */
class AConstructionAfterAnEvaluationThatAnswersNothingIsNotJudgedTest {

    /** The smallest {@code Int}, written as the sum it has to be written as: the literal itself is
     * one past the largest. */
    private static final String SMALLEST = "(0 - 9223372036854775807) - 1";

    private static final String DECLARATIONS = """
            module demo

            data Negative = Int
                invariant value < 0

            data Nothing

            """;

    /** Every code the compile reports, with a refusal read as the code it refused with — so that a
     * row which stops the compile and a row which warns are read off one answer. */
    private static List<String> reported(String source) {
        try {
            return Compiler.compileWithWarnings(source).warnings().stream()
                    .map(Diagnostic::code)
                    .distinct()
                    .toList();
        } catch (souther.compiler.diag.CompileException refused) {
            String said = refused.getMessage();
            int at = said.indexOf("E2");
            return List.of(at < 0 ? said : said.substring(at, at + 5));
        }
    }

    /** A behavior that divides and builds a {@code Negative} from {@code built} in the value arm,
     * under {@code guards}. */
    private static String dividing(String guards, String divisor, String built) {
        return DECLARATIONS + """
                behavior 割る : (a: Int, x: Int) -> Negative | Nothing
                    constructs Negative
                let 割る (a, x) = {
                %s    match Int.divide(a, %s) with
                        | Int as q -> Negative(%s)
                        | DivisionByZero -> Nothing
                }
                """.formatted(guards, divisor, built);
    }

    private static String guard(String condition) {
        return "    guard " + condition + " else Nothing\n";
    }

    /**
     * The one pair, with the divisor written out so that no other case can come back: the number is
     * one no run computes and {@code DivisionByZero} is one no run answers, so the operation answers
     * nothing at all and neither arm is entered.
     *
     * <p>Read twice over, with the construction built from the quotient and from something else.
     * Which of the two an author writes is exactly what used to decide it — the first was owed its
     * clause because nothing was known of {@code q}, the second refused because {@code x >= 0}
     * really does refute {@code value < 0} — and neither answer was about the arm.
     */
    @Test
    void anOperationWithNoNumberAndNoOtherCaseLeavesTheArmsUnentered() {
        assertEquals(List.of(), reported(dividing(guard("a == " + SMALLEST), "0 - 1", "q")),
                "the quotient the arm binds");
        assertEquals(List.of(),
                reported(dividing(guard("a == " + SMALLEST) + guard("x >= 0"), "0 - 1", "x")),
                "a value the guards decide, which is the same arm and so the same answer");
    }

    /**
     * The same operands, with the divisor a value the guards hold away from zero rather than a
     * number written out. What rules the other case out is what is known of the argument and not how
     * it was spelled.
     */
    @Test
    void theOtherCaseIsRuledOutByWhatIsKnownAndNotByHowItIsWritten() {
        assertEquals(List.of(),
                reported(dividing(guard("a == " + SMALLEST) + guard("x == 0 - 1"), "x", "q")),
                "the divisor is held to minus one, so no case comes back");
    }

    /**
     * The divisor is minus one or zero, so the divide answers nothing down one of them and
     * {@code DivisionByZero} down the other. A run leaves the operation, the arms are entered, and
     * what is written under them is judged as it always was.
     */
    @Test
    void anOtherCaseThatMayComeBackIsARunCarryingOn() {
        assertEquals(List.of("E2011"),
                reported(dividing(guard("a == " + SMALLEST) + guard("x <= 0") + guard("x >= 0 - 1"),
                        "x", "q")),
                "the divide may come back as its other case, so the arms are entered");
    }

    /**
     * The dividend is the smallest {@code Int} or nought, so the quotient is a number for one of
     * them. The operation answers, and the construction over what it answered is judged on its
     * value: nought is not negative, and the refusal is the ordinary one.
     */
    @Test
    void aDividendWithOnePairThatAnswersIsNotAnAbort() {
        assertEquals(List.of("E2010"),
                reported(dividing(guard("a >= " + SMALLEST) + guard("a <= 0"), "0 - 1", "q")),
                "some pair answers, so nothing here is shown to abort");
    }

    /**
     * A product that overflows for every value admitted, and one that overflows for some. The rule
     * is the recipe's and not the divide's, so it is the same rule in both spellings and for both
     * operations — and it is the operator here, which aborts rather than answering a case.
     *
     * <p>The second is the control the first needs. Its product is at or above nought for every
     * factor admitted, which is exactly what {@code Negative} rejects, so the construction is
     * refused — the rule ran, the arithmetic was read, and the value was judged on it. What the
     * first row does is stop that from happening, and it can only be read against a row where it
     * happens.
     */
    @Test
    void theSameHoldsOfEveryOperationARecipeIsWrittenFor() {
        assertEquals(List.of(), reported(DECLARATIONS + """
                behavior 掛ける : (a: Int, x: Int) -> Negative | Nothing
                    constructs Negative
                let 掛ける (a, x) = {
                    guard a >= 5000000000 else Nothing
                    guard x >= 0 else Nothing
                    Negative(a * a)
                }
                """), "every product of two such values is a number no `Int` is");
        assertEquals(List.of("E2010"), reported(DECLARATIONS + """
                behavior 掛ける : (a: Int, x: Int) -> Negative | Nothing
                    constructs Negative
                let 掛ける (a, x) = {
                    guard a >= 0 else Nothing
                    guard x >= 0 else Nothing
                    Negative(a * a)
                }
                """), "a product that overflows for some pairs and answers for others is judged on"
                        + " what it answers, and this one answers a number no `Negative` is");
    }

    /**
     * A field standing after one whose value aborts, and the same two fields the other way round.
     *
     * <p>The stop is not about a binding or an arm. `Pair` declares `l` and then `r`, and that is
     * the order they run in, so the construction is after the abort in one of these and before it
     * in the other — one program written two ways, and the answer follows the order.
     */
    @Test
    void aSiblingAfterAnAbortingOneIsNotJudgedAndOneBeforeItIs() {
        assertEquals(List.of(), reported(overflowingBeside(
                "l = Negative(0 - a * a), r = Negative(x)")),
                "the overflowing field runs first, so nothing after it is reached");
        assertEquals(List.of("E2010"), reported(overflowingBeside(
                "l = Negative(x), r = Negative(0 - a * a)")),
                "and the very same construction runs first the other way round, where it is judged"
                        + " and refused — which is what the row above must not reach");
    }

    /** A pair of {@code Negative}s built where {@code a * a} is a number no {@code Int} is and
     * {@code x} is at or above nought, so one field aborts and the other is refused. */
    private static String overflowingBeside(String fields) {
        return DECLARATIONS + """
                data Pair = { l: Negative, r: Negative }

                behavior 組む : (a: Int, x: Int) -> Pair | Nothing
                    constructs Pair, Negative
                let 組む (a, x) = {
                    guard a >= 5000000000 else Nothing
                    guard x >= 0 else Nothing
                    Pair { %s }
                }
                """.formatted(fields);
    }

    /**
     * An operand a short-circuiting operator does not always evaluate, in both directions.
     *
     * <p>{@code &&} stops as soon as its left comes out false (spec
     * §a-condition-stops-when-its-answer-is-settled), so its right runs on the runs the left came
     * out true on and on no others. That makes it a branch and not a step, and both directions go
     * wrong where it is read as a step: what it aborts on stops runs it never ran on, and what it
     * builds is judged on runs it was never built on.
     *
     * <p>Read as the same expression with the two operands the other way round, because that is the
     * one difference: on the left it runs whenever the operator does, and on the right it runs
     * where the left came out true. Nothing else about either program changes.
     */
    @Test
    void anOperandAShortCircuitDoesNotAlwaysEvaluateIsABranch() {
        assertEquals(List.of("E2010"), reported(shortCircuiting(
                "x < 0 && a * a > 0", "if flag then Nothing else Negative(x)",
                "    guard x >= 0 else Nothing\n")),
                "the product that overflows runs only where the left came out true, which is"
                        + " nowhere here — so it stops nothing and the construction is judged");
        assertEquals(List.of(), reported(shortCircuiting(
                "x < 0 && Negative(x).value < 0", "if flag then Nothing else Nothing",
                "    guard x >= 0 else Nothing\n")),
                "and a construction on that side is built on no run, so it is not judged");
        assertEquals(List.of("E2010"), reported(shortCircuiting(
                "Negative(x).value < 0 && x < 0", "if flag then Nothing else Nothing",
                "    guard x >= 0 else Nothing\n")),
                "the very same construction on the side that always runs is judged, which is what"
                        + " says the row above is about where it stands and not about what it is");
    }

    /** A behavior that binds {@code condition} and answers {@code body}, under a guard that holds
     * {@code a} where every product of it overflows and whatever else {@code more} guards. */
    private static String shortCircuiting(String condition, String body, String more) {
        return DECLARATIONS + """
                behavior f : (a: Int, x: Int) -> Negative | Nothing
                    constructs Negative
                let f (a, x) = {
                    guard a >= 5000000000 else Nothing
                %s    let flag = %s
                    %s
                }
                """.formatted(more, condition, body);
    }

    /**
     * What a short-circuiting operator leaves is what its two ways leave, and a way that reaches
     * nothing is not one of them.
     *
     * <p>The rows above hold the side that does not run. These hold the other half: the operator is
     * a fork with two ways on — the runs that evaluated the right operand, and the runs the left
     * already answered for — and a run leaves it down one of them. So an operand that always runs
     * and always aborts leaves no way at all, and one that aborts on the side it runs leaves only
     * the side it does not.
     *
     * <p>The second is what says this carries more than a flag. Where the right operand is the only
     * way that closes, every run that reaches what comes after came the other way, and it comes
     * carrying what that way settled — {@code x < 0} here, which discharges the construction that
     * would otherwise be owed its clause.
     */
    @Test
    void whatAShortCircuitLeavesIsWhatItsWaysLeave() {
        assertEquals(List.of(), reported(shortCircuiting(
                "x >= 0 && a * a > 0", "Negative(x)", "    guard x >= 0 else Nothing\n")),
                "the right operand runs on every run that gets here and aborts on every one of"
                        + " them, so there is no way on");
        assertEquals(List.of("E2010"), reported(shortCircuiting(
                "x >= 0 && a > 0", "Negative(x)", "    guard x >= 0 else Nothing\n")),
                "and the same shape with nothing that aborts leaves both ways, so the construction"
                        + " is judged — which is what says the row above is about the abort");
        assertEquals(List.of(), reported(shortCircuiting(
                "x >= 0 && a * a > 0", "Negative(x)", "")),
                "the only way on is the one the left answered for, so what it settled — `x < 0` —"
                        + " holds where the construction stands, and discharges it");
        assertEquals(List.of("E2011"), reported(shortCircuiting(
                "x >= 0 && a > 0", "Negative(x)", "")),
                "and with both ways left there is nothing to carry, so the clause stands owed");
        assertEquals(List.of(), reported(shortCircuiting(
                "x < 0 || a * a > 0", "Negative(x)", "")),
                "an `||` says the same thing the other way round, and the polarity is the"
                        + " operator's to give");
    }

    /**
     * A closure a combinator applies is read where it runs, which is after every argument has
     * answered.
     *
     * <p>{@code List.map} takes the function before the container, so the body used to be read while
     * the argument list was still being walked — before the container was evaluated, and on runs
     * the container's own evaluation stops. A container that aborts means the operation is never
     * entered and the closure never applied.
     */
    @Test
    void aClosureACombinatorAppliesIsReadAfterEveryArgumentHasAnswered() {
        assertEquals(List.of(), reported(mapping("[a * a]")),
                "the container aborts, so the operation is not entered and the body never runs");
        assertEquals(List.of("E2010"), reported(mapping("[a]")),
                "and over a container that answers, the same body is read and the value refused");
    }

    /** A behavior that maps a closure building a {@code Negative} over {@code container}. */
    private static String mapping(String container) {
        return DECLARATIONS + """
                behavior f : (a: Int, x: Int) -> Negative | Nothing
                    constructs Negative
                let f (a, x) = {
                    guard a >= 5000000000 else Nothing
                    guard x >= 0 else Nothing
                    let ys = List.map(y -> Negative(x), %s)
                    Nothing
                }
                """.formatted(container);
    }

    /**
     * A divide by nought, which answers no number whichever way it is spelled — and the two
     * spellings, which do not answer alike.
     *
     * <p>The operator aborts on a zero divisor; {@code Int.divide} comes back as
     * {@code DivisionByZero}, which is a case an arm is reached at (spec §stdlib-int). So the same
     * divisor settles the question one way for one of them and does not settle it at all for the
     * other, and what tells them apart is the operation's own cases and not the divisor.
     */
    @Test
    void aDivideByNoughtIsAnAbortForTheOperatorAndACaseForTheFunction() {
        assertEquals(List.of(), reported(DECLARATIONS + """
                behavior 割る : (x: Int) -> Negative | Nothing
                    constructs Negative
                let 割る (x) = {
                    guard x >= 0 else Nothing
                    guard x / 0 > 1 else Nothing
                    Negative(x)
                }
                """), "the operator aborts on nought, so nothing after it is reached");
        assertEquals(List.of("E2010"), reported(DECLARATIONS + """
                behavior 割る : (x: Int) -> Negative | Nothing
                    constructs Negative
                let 割る (x) = {
                    guard x >= 0 else Nothing
                    match Int.divide(x, 0) with
                        | Int as q -> Nothing
                        | DivisionByZero -> Negative(x)
                }
                """), "the function answers a case for the same divisor, and that arm is reached");
    }

    /**
     * A {@code Decimal} divide at a scale the run time cannot take, which aborts as an overflow does
     * (spec §stdlib-decimal). The rule is the operand's and not the arithmetic's, so it is the same
     * rule as the divisor's and it reaches the same answer.
     */
    @Test
    void aDivideAtAScaleTheRunTimeCannotTakeLeavesTheArmUnentered() {
        assertEquals(List.of(), reported(atScale("4294967298")),
                "no run leaves the divide, so the construction the arm builds is not judged");
        assertEquals(List.of("E2010"), reported(atScale("2")),
                "and at a scale it does take the arm is entered and the value is refused");
    }

    /** A {@code Decimal} divide by a divisor held off nought, building a {@code Negative} the values
     * refuse. */
    private static String atScale(String places) {
        return DECLARATIONS + """
                behavior 割る : (x: Decimal, y: Decimal, n: Int) -> Negative | Nothing
                    constructs Negative
                let 割る (x, y, n) = {
                    guard y >= 1m else Nothing
                    guard n >= 0 else Nothing
                    match Decimal.divide(x, y, %s, HALF_UP) with
                        | Decimal as q -> Negative(n)
                        | DivisionByZero -> Nothing
                }
                """.formatted(places);
    }

    /**
     * An {@code unreachable} written in an earlier field, which answers nothing for a reason the
     * tree alone gives.
     *
     * <p>Beside the rows above rather than one of them, because what shows it is different in kind:
     * nothing about the path enters into it, and it is what
     * {@link souther.compiler.coverage.NormalReturn} answers without one. What follows from it is
     * the same, which is the point of there being one answer for a continuation to be given.
     */
    @Test
    void anUnreachableInAnEarlierFieldLeavesTheFieldAfterItUnjudged() {
        assertEquals(List.of(), reported(DECLARATIONS + """
                data Pair = { l: Negative, r: Negative }

                behavior 組む : (x: Int) -> Pair | Nothing
                    constructs Pair, Negative
                let 組む (x) = {
                    guard x >= 0 else Nothing
                    Pair { l = unreachable "the model says so", r = Negative(x) }
                }
                """), "the first field answers nothing, so the second is evaluated on no run");
        assertEquals(List.of("E2010"), reported(DECLARATIONS + """
                data Pair = { l: Negative, r: Negative }

                behavior 組む : (x: Int) -> Pair | Nothing
                    constructs Pair, Negative
                let 組む (x) = {
                    guard x >= 0 else Nothing
                    Pair { l = Negative(x), r = unreachable "the model says so" }
                }
                """), "and the same two fields the other way round put it where runs reach it");
    }

    /**
     * A construction evaluated before the abort is a construction the program builds, and it is
     * judged.
     *
     * <p>The one row that tells an evaluation nothing leaves from a place nothing arrives at. Read
     * as the second, the whole expression would go unwalked and this would fall silent — which is
     * the same defect over again, written on the other side of the abort.
     */
    @Test
    void aConstructionEvaluatedBeforeTheAbortIsStillJudged() {
        assertEquals(List.of("E2010"), reported(DECLARATIONS + """
                behavior 割る : (a: Int, x: Int) -> Negative | Nothing
                    constructs Negative
                let 割る (a, x) = {
                    guard a == %s else Nothing
                    guard x >= 0 else Nothing
                    let 先に = Negative(x)
                    match Int.divide(a, 0 - 1) with
                        | Int as q -> 先に
                        | DivisionByZero -> Nothing
                }
                """.formatted(SMALLEST)),
                "the binding runs before the divide does, so the value it builds is one the program"
                        + " really builds");
    }
}
