package souther.compiler;

import souther.compiler.diag.Diagnostic;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A truncating divide says how what it answered stands to what it divided, and not only where its
 * answer lies.
 *
 * <p>A quotient's own range comes off its dividend's and its divisor's, so ten times a quotient at
 * or above nought is at or above nought — and what is <em>left</em> of the dividend was a value
 * nothing put on either side of nought (#960). That is the value every step of a change-making loop
 * is built on: the first denomination discharged and the second did not, because what the first left
 * was unknown and so was the quotient taken of it.
 *
 * <p>What holds is not {@code 0 <= a - b * (a / b) < b} in general. {@code /} truncates toward zero
 * (spec §stdlib-int), so what is left keeps the sign of the <em>dividend</em> and is smaller than
 * the <em>magnitude</em> of the divisor: {@code -7 / 2} is {@code -3} and {@code -7 - 2 * -3} is
 * {@code -1}, and {@code 7 / -10} is nought and leaves seven. Which side the dividend is on is what
 * the path establishes, and it is read where the clause is read, as a product's bound is.
 */
class AQuotientIsHeldAgainstWhatItDividedTest {

    private static String model(String guard, String construction) {
        return """
                module demo

                data 硬貨枚数 = Int
                    invariant value >= 0

                behavior 買う : (額: Int) -> 硬貨枚数
                    constructs 硬貨枚数

                let 買う (額) = {
                    guard %s else 硬貨枚数(0)
                    %s
                }
                """.formatted(guard, construction);
    }

    private static List<String> reported(String guard, String construction) {
        return Compiler.compileWithWarnings(model(guard, construction)).warnings().stream()
                .map(Diagnostic::code)
                .distinct()
                .toList();
    }

    /** The quotient's own range, which came off its operands before any of this. */
    @Test
    void theQuotientsOwnRangeIsStillRead() {
        assertEquals(List.of(), reported("額 >= 0", "硬貨枚数(額 / 10)"));
        assertEquals(List.of(), reported("額 >= 0", "硬貨枚数(額 / 10 * 10)"));
    }

    /** What the divide left, which is the quotient held against the very value it was taken of. */
    @Test
    void whatTheDivideLeftIsAtOrAboveNought() {
        assertEquals(List.of(), reported("額 >= 0", "硬貨枚数(額 - 額 / 10 * 10)"));
    }

    /**
     * The other half of the relation: what is left is below the divisor, which is what says the next
     * denomination's quotient is bounded. Ninety-nine is what a hundred leaves at most, so nine is
     * what ten of that answers at most — and a count of nine is a count of at least nought.
     */
    @Test
    void whatTheDivideLeftIsBelowTheDivisor() {
        assertEquals(List.of(), reported("額 >= 0", """
                {
                        let k0 = 額 / 100
                        let r0 = 額 - k0 * 100
                        let k1 = r0 / 10
                        硬貨枚数(k0 + k1)
                    }"""));
    }

    /** The same through the total surface, which is where an author writes it when the divisor is
     * not a literal they can argue about. */
    @Test
    void theSameHoldsOfTheValueCaseOfADivide() {
        assertEquals(List.of(), reported("額 >= 0", """
                match Int.divide(額, 10) with
                        | Int as k -> 硬貨枚数(額 - k * 10)
                        | DivisionByZero -> 硬貨枚数(0)"""));
    }

    /** The remainder answered as its own value, which the library has an operation for. */
    @Test
    void aRemainderIsAtOrAboveNoughtAndBelowItsDivisor() {
        assertEquals(List.of(), reported("額 >= 0", """
                match Int.truncatingRemainder(額, 10) with
                        | Int as r -> 硬貨枚数(9 - r)
                        | DivisionByZero -> 硬貨枚数(0)"""));
    }

    /**
     * The sign is the dividend's, so a dividend the guards leave on either side of nought leaves
     * what the divide left there too.
     *
     * <p>The control the rest of them need: this is the very construction of
     * {@link #whatTheDivideLeftIsAtOrAboveNought} under a guard that says nothing about which side
     * the dividend is on, and it is reported.
     */
    @Test
    void withTheDividendOnNeitherSideOfNoughtNothingFollows() {
        assertEquals(List.of("E2011"), reported("額 <= 1000", "硬貨枚数(額 - 額 / 10 * 10)"));
    }

    /** And with the dividend at or below nought, what is left is at or below nought — which the
     * construction owing {@code value >= 0} is refused by, not discharged. */
    @Test
    void aDividendAtOrBelowNoughtLeavesSomethingAtOrBelowIt() {
        assertEquals(List.of(), reported("額 <= 0", "硬貨枚数(額 / 10 * 10 - 額)"));
    }

    /**
     * A negative divisor leaves something of the dividend's sign and smaller than the divisor's
     * magnitude, which is what the relation says and is not what {@code 0 <= r < b} would say.
     *
     * <p>{@code 額 / -10 * -10} is the multiple of ten at or below the dividend for a non-negative
     * dividend, so what is left is at or above nought — over a divisor on the other side of it.
     */
    @Test
    void aNegativeDivisorLeavesSomethingOfTheDividendsSign() {
        assertEquals(List.of(), reported("額 >= 0", "硬貨枚数(額 - 額 / (0 - 10) * (0 - 10))"));
    }

    /**
     * The divisor is what the reading holds it to and not what was written at the divide.
     *
     * <p>A name given a constant is that constant, and so is a value a guard pins. Asked of how the
     * divide was written, the magnitude half said nothing wherever the divisor was anything but a
     * written number: the two sign facts arrived and {@code -100 < r < 100} did not, though the
     * reading held the divisor to one number.
     */
    @Test
    void aDivisorAGuardPinsIsADivisor() {
        assertEquals(List.of(), pinned("""
                match Int.truncatingRemainder(額, 額面) with
                            | Int as r -> 硬貨枚数(99 - r)
                            | DivisionByZero -> 硬貨枚数(0)"""),
                "a hundred leaves ninety-nine at most, so ninety-nine less it is at or above nought");
    }

    /**
     * The same of a quotient held against what it divided, where the construction is written over
     * the multiple rather than over what is left of it.
     *
     * <p>The multiply is by the written number and the divide is by the name, which is what makes
     * this a form the domain carries: {@code 額 / 額面 * 額面} is a product of two values the
     * fragment holds as one atom, and relating that atom to the quotient is a rule this does not
     * have.
     */
    @Test
    void aQuotientOverADivisorAGuardPinsIsHeldAgainstItToo() {
        assertEquals(List.of(), pinned("硬貨枚数(額 - 額 / 額面 * 100)"));
    }

    /** The two above, under a guard that pins the divisor to one number. */
    private static List<String> pinned(String construction) {
        return Compiler.compileWithWarnings("""
                module demo

                data 硬貨枚数 = Int
                    invariant value >= 0

                behavior 買う : (額: Int, 額面: Int) -> 硬貨枚数
                    constructs 硬貨枚数
                let 買う (額, 額面) = {
                    guard 額 >= 0 else 硬貨枚数(0)
                    guard 額面 == 100 else 硬貨枚数(0)
                    %s
                }
                """.formatted(construction)).warnings().stream()
                .map(Diagnostic::code).distinct().toList();
    }

    /**
     * Taking the {@code DivisionByZero} arm establishes that the divisor was zero, which is what
     * that case means and is a fact about a value the caller handed over.
     */
    @Test
    void theFailureArmEstablishesThatTheDivisorWasZero() {
        assertEquals(List.of(), reported("額 <= 100", """
                match Int.divide(100, 額) with
                        | Int as k -> 硬貨枚数(0)
                        | DivisionByZero -> 硬貨枚数(額)"""));
    }

    /**
     * And taking the value arm establishes the denial, which is one statement's other reading and
     * not a second rule.
     */
    @Test
    void theValueArmEstablishesThatTheDivisorWasNot() {
        String model = """
                module demo

                data NonZero = Int
                    invariant notZero = value /= 0

                data Nothing

                behavior 割る : (d: Int) -> NonZero | Nothing
                    constructs NonZero
                let 割る (d) =
                    match Int.divide(100, d) with
                        | Int as k -> NonZero(d)
                        | DivisionByZero -> Nothing
                """;
        assertEquals(List.of(), Compiler.compileWithWarnings(model).warnings().stream()
                .map(Diagnostic::code).distinct().toList());
    }

    /** The control beside both: the value arm says the divisor is not zero and says nothing about
     * which side of nought it is on. */
    @Test
    void theValueArmOnlyEstablishesThatTheDivisorIsNotZero() {
        assertEquals(List.of("E2011"), reported("額 <= 100", """
                match Int.divide(100, 額) with
                        | Int as k -> 硬貨枚数(額)
                        | DivisionByZero -> 硬貨枚数(0)"""));
    }
}
