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
