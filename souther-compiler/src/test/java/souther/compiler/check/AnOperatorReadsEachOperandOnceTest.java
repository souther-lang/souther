package souther.compiler.check;

import souther.compiler.Compiler;
import souther.compiler.core.Core;
import souther.test.Growth;
import souther.test.Visits;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.SequencedMap;
import java.util.function.IntFunction;

/**
 * Elaborating a binary expression reads each operand once, so what it costs is the size of the
 * expression and not two to the power of its nesting depth.
 *
 * <p>An operand read twice costs twice its own subtree, and an operand of an operand costs twice
 * again: a chain of {@code N} operators nested one inside the last cost {@code 2^N}. Nothing said
 * so — the operand check that read them is the same check that reports, and it reports nothing until
 * it comes back.
 *
 * <p>What is counted is how many times a compile goes into the elaborated expressions, at three
 * sizes each double the last. One reading of each operand doubles the count with the chain, and a
 * second reading squares it. The reading is one place for every operator, so a chain of any one of
 * them measures it. A chain of named values is not one of them: a name of constants is folded
 * before an operator is elaborated, so the count of such a chain does not move when an operand is
 * read twice. What a chain of names costs is held by
 * {@link FollowingWhatANameWasGivenCostsTheChainOnceTest}.
 */
class AnOperatorReadsEachOperandOnceTest {

    private static final int[] LINKS = {4, 8, 16};

    @Test
    void aChainOfArithmeticCostsWhatItsLengthSays() {
        assertLinear(links -> """
                module m

                behavior f : (x: Int) -> Int
                let f (x) = x%s
                """.formatted(" + 1".repeat(links)));
    }

    @Test
    void aChainOfAppendsCostsWhatItsLengthSays() {
        assertLinear(links -> """
                module m

                behavior f : (s: String) -> String
                let f (s) = s%s
                """.formatted(" ++ \"a\"".repeat(links)));
    }

    @Test
    void aChainOfLogicalOperatorsCostsWhatItsLengthSays() {
        assertLinear(links -> """
                module m

                behavior f : (b: Bool) -> Bool
                let f (b) = b%s
                """.formatted(" && true".repeat(links)));
    }

    /** `==` does not associate, so the nesting is written out. */
    @Test
    void aChainOfEqualitiesCostsWhatItsLengthSays() {
        assertLinear(links -> """
                module m

                behavior f : (b: Bool) -> Bool
                let f (b) = %sb%s
                """.formatted("(".repeat(links), " == true)".repeat(links)));
    }

    /** Compiles the source {@code of} makes at each size and asks that doubling the chain at most
     *  multiplies by sixteen how often the compile goes into the elaborated expressions: a
     *  polynomial cost is allowed, and a second reading of an operand multiplies the count by two to
     *  the power of the links added, which from eight to sixteen links is far past sixteen. */
    private static void assertLinear(IntFunction<String> of) {
        SequencedMap<Integer, Long> elaborated = new LinkedHashMap<>();
        try (Visits visits = Visits.into(List.of(Core.class))) {
            for (int links : LINKS) {
                String source = of.apply(links);
                elaborated.put(links, visits.during(() -> Compiler.compile(source)));
            }
        }
        Growth.eachAtMost(elaborated, 16, 1);
    }
}
