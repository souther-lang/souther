package souther.compiler.check;

import souther.compiler.Compiler;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * An operation that answers one of the values it was given is read as the cases its definition is
 * written in: which argument it answers, and what holds of the arguments where it answers that one.
 * A clause holds of the result exactly when it holds in every case, and fails of it when it fails in
 * every case that is reached at all.
 *
 * <p>Stated case by case rather than as a bound on the result, because a bound would have to hold
 * whatever the arguments are. {@code Int.clamp(lo, hi, n)} is total and does not ask that {@code lo}
 * be below {@code hi}: where it is not, the result is not inside both of them, and the rule that
 * said it was would prove a clause the values can fail.
 */
class AnOperationThatChoosesIsReadCaseByCaseTest {

    private static final String TYPES = """
            module demo
            data NonNeg = Int
                invariant value >= 0
            data Pct = Int
                invariant value >= 0 && value <= 100
            data AtLeastFifty = Int
                invariant value >= 50
            data AboveTen = Int
                invariant value > 10
            data Middle = Int
                invariant value > 4 && value < 6
            data Bad
            """;

    private static List<String> codesOf(String module) {
        return Compiler.compileWithWarnings(module).warnings().stream()
                .map(Diagnostic::code)
                .toList();
    }

    @Test
    void aSmallerOfTwoIsWhatBothOfThemAre() {
        assertEquals(List.of(), codesOf(TYPES + """
                behavior smaller : (a: Int, b: Int) -> NonNeg | Bad constructs NonNeg, Bad
                let smaller (a, b) = {
                    guard a >= 0
                        else Bad
                    guard b >= 0
                        else Bad
                    NonNeg(Int.min(a, b))
                }
                """));
    }

    @Test
    void aLargerOfTwoIsAtLeastEitherOfThem() {
        assertEquals(List.of(), codesOf(TYPES + """
                behavior atLeastZero : (x: Int) -> NonNeg constructs NonNeg
                let atLeastZero (x) = NonNeg(Int.max(0, x))
                """));
    }

    @Test
    void aClampedValueIsInsideBoundsWrittenTheRightWayRound() {
        assertEquals(List.of(), codesOf(TYPES + """
                behavior score : (x: Int) -> Pct constructs Pct
                let score (x) = Pct(Int.clamp(0, 100, x))
                """));
    }

    /**
     * The case that answers the value itself, on its own. What the path knows of that value puts
     * both ends out of reach — a value above four is not below zero, and one below six is not above
     * ten — so the clause is established by the third case and by nothing else.
     */
    @Test
    void aClampedValueInsideBothEndsIsTheValueItself() {
        assertEquals(List.of(), codesOf(TYPES + """
                behavior narrow : (n: Int) -> Middle | Bad constructs Middle, Bad
                let narrow (n) = {
                    guard n > 4
                        else Bad
                    guard n < 6
                        else Bad
                    Middle(Int.clamp(0, 10, n))
                }
                """));
    }

    @Test
    void aClampWhoseBoundsAreTheWrongWayRoundEstablishesNeither() {
        assertEquals(List.of("E2011"), codesOf(TYPES + """
                behavior score : (x: Int) -> AtLeastFifty constructs AtLeastFifty
                let score (x) = AtLeastFifty(Int.clamp(50, 0, x))
                """));
    }

    @Test
    void aSmallerOfTwoIsNotEstablishedByTheFirstOfThemAlone() {
        assertEquals(List.of("E2011"), codesOf(TYPES + """
                behavior smaller : (a: Int, b: Int) -> NonNeg | Bad constructs NonNeg, Bad
                let smaller (a, b) = {
                    guard a >= 0
                        else Bad
                    NonNeg(Int.min(a, b))
                }
                """));
    }

    @Test
    void aSmallerOfTwoIsNotEstablishedByTheSecondOfThemAlone() {
        assertEquals(List.of("E2011"), codesOf(TYPES + """
                behavior smaller : (a: Int, b: Int) -> NonNeg | Bad constructs NonNeg, Bad
                let smaller (a, b) = {
                    guard b >= 0
                        else Bad
                    NonNeg(Int.min(a, b))
                }
                """));
    }

    @Test
    void aLargerOfTwoIsNotHeldDownByTheFirstOfThemAlone() {
        assertEquals(List.of("E2011"), codesOf(TYPES + """
                behavior larger : (a: Int, b: Int) -> Pct | Bad constructs Pct, Bad
                let larger (a, b) = {
                    guard a >= 0 && a <= 100
                        else Bad
                    guard b >= 0
                        else Bad
                    Pct(Int.max(a, b))
                }
                """));
    }

    @Test
    void aLargerOfTwoIsNotHeldDownByTheSecondOfThemAlone() {
        assertEquals(List.of("E2011"), codesOf(TYPES + """
                behavior larger : (a: Int, b: Int) -> Pct | Bad constructs Pct, Bad
                let larger (a, b) = {
                    guard a >= 0
                        else Bad
                    guard b >= 0 && b <= 100
                        else Bad
                    Pct(Int.max(a, b))
                }
                """));
    }

    /**
     * A guard about the call itself and the cases the call is defined in are two readings of one
     * value, and they have to agree. Where the guards cannot all hold, they disagree about what
     * cannot happen — the case reading finds no case left, the reading that takes the call as an
     * unknown still has the guard's bound — and a clause that came out established by one and
     * refused by the other is a check contradicting itself rather than an answer.
     */
    @Test
    void aGuardAboutTheCallItselfIsReadAlongsideTheCases() {
        String module = TYPES + """
                behavior odd : (a: Int, b: Int) -> AboveTen | Bad constructs AboveTen, Bad
                let odd (a, b) = {
                    guard a >= 10
                        else Bad
                    guard b >= 10
                        else Bad
                    guard Int.min(a, b) <= 3
                        else Bad
                    AboveTen(Int.min(a, b))
                }
                """;
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(module));
        assertEquals("E2010", e.diagnostic().code(),
                "the guard puts the value below what the invariant asks: " + e.getMessage());
    }

    @Test
    void aChoiceEveryCaseOfWhichFailsIsRefused() {
        String module = TYPES + """
                behavior small : (x: Int) -> AboveTen constructs AboveTen
                let small (x) = AboveTen(Int.min(0, x))
                """;
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(module));
        assertEquals("E2010", e.diagnostic().code(),
                "a smaller of two, neither of which can be above ten, is a definite violation: "
                        + e.getMessage());
    }
}
