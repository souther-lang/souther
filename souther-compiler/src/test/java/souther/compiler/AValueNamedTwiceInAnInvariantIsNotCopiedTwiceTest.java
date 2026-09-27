package souther.compiler;

import org.junit.jupiter.api.Test;

import java.time.Duration;
import java.util.function.UnaryOperator;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;

/**
 * A chain of values in which each names the one before it twice is as long as the source wrote it,
 * and an {@code invariant} that names the last of them is read as long as that, whichever of the
 * representations of the clause reads it.
 */
class AValueNamedTwiceInAnInvariantIsNotCopiedTwiceTest {

    private static final Duration WHAT_A_LINEAR_EXPANSION_TAKES = Duration.ofSeconds(20);

    private static String chain(int links, String first, String operator, String type) {
        return chainOf(links, first, previous -> previous + " " + operator + " " + previous,
                "value > c" + links, type);
    }

    /** {@code links} values, each written as {@code link} of the one before it, and an invariant
     *  stating {@code rule} of the last. */
    private static String chainOf(int links, String first, UnaryOperator<String> link,
                                  String rule, String type) {
        StringBuilder source = new StringBuilder("module m exposing ( D, f )\n\nlet c0 = " + first + "\n");
        for (int at = 1; at <= links; at++) {
            source.append("let c%d = %s\n".formatted(at, link.apply("c" + (at - 1))));
        }
        source.append("""

                data D = %s
                    invariant %s

                behavior f : (d: D) -> Int
                let f (d) = 1
                """.formatted(type, rule));
        return source.toString();
    }

    private static void compilesAtTheCostOfTheSource(String source) {
        assertTimeoutPreemptively(WHAT_A_LINEAR_EXPANSION_TAKES,
                () -> assertDoesNotThrow(() -> Compiler.compile(source)));
    }

    private static String doublingChain(int links) {
        StringBuilder chain = new StringBuilder("module m exposing ( f )\n\nlet c0 = 2\n");
        for (int at = 1; at <= links; at++) {
            chain.append("let c%d = c%d + c%d\n".formatted(at, at - 1, at - 1));
        }
        return chain.toString();
    }

    @Test
    void aBehaviorBodyThatNamesTheChainIsCompiled() {
        compilesAtTheCostOfTheSource(doublingChain(30)
                + "\nbehavior f : (n: Int) -> Int\nlet f (n) = n + c30\n");
    }

    @Test
    void aHelperThatNamesTheChainIsCompiled() {
        compilesAtTheCostOfTheSource(doublingChain(30)
                + "\nlet h (n: Int) = n + c30\nbehavior f : (n: Int) -> Int\nlet f (n) = h(n)\n");
    }

    /** A parameter the author left untyped is one the helper's body is read to settle. */
    @Test
    void aHelperWithAParameterToSettleThatNamesTheChainIsCompiled() {
        compilesAtTheCostOfTheSource(doublingChain(30)
                + "\nlet h (x) = x + c30\nbehavior f : (n: Int) -> Int\nlet f (n) = h(n)\n");
    }

    @Test
    void aHelperTheModulePublishesThatNamesTheChainIsCompiled() {
        compilesAtTheCostOfTheSource(doublingChain(30).replace("exposing ( f )", "exposing ( f, h )")
                + "\nlet h (n: Int) = n + c30\nbehavior f : (n: Int) -> Int\nlet f (n) = h(n)\n");
    }

    @Test
    void anEnsuresThatNamesTheChainIsCompiled() {
        compilesAtTheCostOfTheSource(doublingChain(30)
                + "\nbehavior f : (n: Int) -> Int\n    ensures value > n + c30\nlet f (n) = n + c30 + 1\n");
    }

    @Test
    void aBooleanChainMuchLongerThanACopyCouldBeBuiltIsCompiled() {
        compilesAtTheCostOfTheSource(chain(200, "true", "&&", "Int").replace("value > c200", "c200"));
    }

    @Test
    void aChainOfDecimalsTakenPastTheEndOfTheScaleRangeIsCompiled() {
        compilesAtTheCostOfTheSource(chain(34, "0.1m", "*", "Decimal"));
    }

    @Test
    void aChainThroughAnOperationTheFoldDoesNotSettleIsCompiled() {
        compilesAtTheCostOfTheSource(chainOf(30, "2",
                previous -> "Int.min(" + previous + ", " + previous + ")", "value > c30", "Int"));
    }

    @Test
    void anIntegerChainLongerThanACopyCouldBeBuiltIsCompiled() {
        String source = chain(30, "2", "+", "Int");

        assertTimeoutPreemptively(WHAT_A_LINEAR_EXPANSION_TAKES,
                () -> assertDoesNotThrow(() -> Compiler.compile(source)));
    }

    @Test
    void aChainOfDecimalsSquaredIntoTheEndOfTheScaleRangeIsCompiled() {
        String source = chain(30, "0.1m", "*", "Decimal");

        assertTimeoutPreemptively(WHAT_A_LINEAR_EXPANSION_TAKES,
                () -> assertDoesNotThrow(() -> Compiler.compile(source)));
    }
}
