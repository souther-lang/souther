package souther.compiler.check;

import souther.compiler.Compiler;
import souther.compiler.check.InvariantChecker.Said;
import souther.compiler.check.InvariantChecker.Verdict;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * What a helper answers is a value the check can name, and whether the reading it is given expanded
 * that helper into the body is not part of the question (issue #722).
 *
 * <p>The reading the check reads keeps the language's own operations standing and expands a module's
 * own {@code let}s into the body it was called from (spec §invariant-discharge-representation). A
 * helper that recurses cannot be expanded, so it stays a call — and a call was a shape the naming had
 * no case for, so a construction over one was left to the run-time check while the same construction
 * over a helper that happens not to recurse was reported. Recursion is a fact about the helper's own
 * body; the value it answers is a function of what it was given either way.
 *
 * <p>What makes it nameable is what the name was resolved to: a module's own helper is pure and
 * total (spec §fn-rules), so two writings of one call with the same arguments are one value. What a
 * behavior answers is named by nothing, and that is here too — both spellings of it, so that the
 * rule is read as being about the callee rather than about which of them was expanded.
 */
class AHelperCallIsNameableWhetherOrNotItWasExpandedTest {

    private static final String TYPES = """
            module demo

            data NonNeg = Int
                invariant nonNegative = value >= 0

            data TooSmall
            """;

    /** The construction over what the helper answered, with nothing known about it. */
    private static String unguarded(String helper) {
        return TYPES + """

                %s

                behavior go : (n: Int) -> NonNeg
                    constructs NonNeg
                let go (n) = NonNeg(step(n))
                """.formatted(helper);
    }

    /** The same, with a guard about the call. */
    private static String guarded(String helper) {
        return TYPES + """

                %s

                behavior go : (n: Int) -> NonNeg | TooSmall
                    constructs NonNeg, TooSmall
                let go (n) = {
                    guard step(n) >= 0 else TooSmall
                    NonNeg(step(n))
                }
                """.formatted(helper);
    }

    private static final String EXPANDED = "let step (n: Int): Int = n - 1";
    private static final String STANDING =
            "partial let step (n: Int): Int = if n <= 0 then n - 1 else step(n - 1)";

    /**
     * Both are unproven, and a guard about the call establishes both.
     *
     * <p>The guard is what says the report is not a trap. A construction is reported only where a
     * guard could silence it, so a call the check names has to be one an author can write a guard
     * about — and the guard that does it here says of the call exactly what the clause needs.
     */
    @ParameterizedTest(name = "{0}")
    @ValueSource(strings = {EXPANDED, STANDING})
    void aHelperCallIsNamedByItsCall(String helper) {
        reads(Verdict.UNKNOWN, unguarded(helper));
        reads(Verdict.PROVED, guarded(helper));
    }

    /**
     * What a behavior answers is named by nothing, whichever way it is reached.
     *
     * <p>Held beside the helper because the two used to differ by which of them this reading had
     * expanded. They differ by what was called.
     */
    @Test
    void aBehaviorsAnswerIsNamedByNothing() {
        reads(Verdict.UNREPRESENTABLE, TYPES + """

                behavior step : (n: Int) -> Int

                behavior go : (n: Int) -> NonNeg
                    constructs NonNeg
                    depends on step
                let go (n, step) = NonNeg(step(n))
                """);
    }

    /**
     * Nothing in a body reaches the naming as a shape it has no term for.
     *
     * <p>Which is the difference {@link Naming.Unsupported} is for. A value nothing can be said of is
     * silent, and so is a shape this compiler has not got round to, and production cannot tell them
     * apart — the run-time check stands either way. So the second is measured rather than reasoned
     * about, over a body that reaches the shapes a fold and a combinator lower into.
     */
    @Test
    void nothingInABodyIsAShapeWithNoTerm() {
        List<String> unsupported = Collections.synchronizedList(new ArrayList<>());
        Terms.UNSUPPORTED = unsupported;
        try {
            Compiler.compileWithWarnings(TYPES + """

                    data Total = Int
                        invariant nonNegative = value >= 0

                    let doubled (xs: List<Int>): List<Int> = List.map(x -> x * 2, xs)

                    behavior go : (xs: List<Int>) -> Total
                        constructs Total
                    let go (xs) = Total(List.sum(doubled(List.filter(x -> x >= 0, xs))))
                    """);
        } finally {
            Terms.UNSUPPORTED = null;
        }

        assertEquals(List.of(), unsupported, "shapes the naming had no term for");
    }

    private static void reads(Verdict expected, String source) {
        List<Said> said = Collections.synchronizedList(new ArrayList<>());
        InvariantChecker.WATCHING = said;
        try {
            Compiler.compileWithWarnings(source);
        } finally {
            InvariantChecker.WATCHING = null;
        }
        List<Verdict> reached = said.stream().map(Said::verdict).toList();
        assertFalse(reached.isEmpty(), "no construction was judged at all");
        assertEquals(List.of(expected), reached);
    }
}
