package souther.compiler.check;

import souther.compiler.Compiler;
import souther.test.Growth;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
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
 * <p>What is counted is the binary expressions elaborated over a compile, at three sizes each
 * double the last. One reading of each operand doubles the count with the chain, and a second
 * reading squares it. The reading is one place for every operator, so a chain of any one of them
 * measures it.
 */
class AnOperatorReadsEachOperandOnceTest {

    private static final int[] LINKS = {3, 6, 12};

    /** A chain of values, each written from the one before it — the shape the nesting ceiling
     *  (E2104) tells an author to break a deep expression into. A value is substituted where it is
     *  named (ADR-0072), so the last one's body is as deep as the chain is long. */
    @Test
    void aChainOfNamedValuesCostsWhatItsLengthSays() {
        assertLinear(links -> {
            StringBuilder source = new StringBuilder("module m\n\nlet v0 = 1\n");
            for (int i = 1; i <= links; i++) {
                source.append("let v").append(i).append(" = v").append(i - 1).append(" + 1\n");
            }
            return source.append("\nbehavior f : (x: Int) -> Int\nlet f (x) = x + v")
                    .append(links).append('\n').toString();
        });
    }

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
     *  at most quintuples the binary expressions elaborated: a polynomial cost is allowed, and a
     *  second reading of an operand multiplies the count by two to the power of the links added. */
    private static void assertLinear(IntFunction<String> of) {
        SequencedMap<Integer, Long> elaborated = new LinkedHashMap<>();
        for (int links : LINKS) {
            long[] counting = {0};
            BinaryElaborator.COUNTING_ELABORATED = counting;
            try {
                Compiler.compile(of.apply(links));
            } finally {
                BinaryElaborator.COUNTING_ELABORATED = null;
            }
            elaborated.put(links, counting[0]);
        }
        Growth.eachAtMost(elaborated, 5, 1);
    }
}
