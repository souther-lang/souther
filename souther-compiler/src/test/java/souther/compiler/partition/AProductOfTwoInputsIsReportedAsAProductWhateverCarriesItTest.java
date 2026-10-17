package souther.compiler.partition;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * Arithmetic no form says is reported as the arithmetic it was, at the positions it is about,
 * whichever way the comparison reaches them: compared directly, handed to an operation over a
 * container, counted, named, written in a helper, under an operation whose form the library states,
 * or written in an invariant.
 *
 * <p>The arithmetic decides which operation it met, where it composes the operands. What a report
 * says is that decision carried through, so a closure or a call around the product changes nothing
 * about it, and nothing is asked of where the value came from to say it again. Held as the pairs of
 * a position and a word, so a reason that reaches one of the two positions a product names and not
 * the other is a failure.
 */
class AProductOfTwoInputsIsReportedAsAProductWhateverCarriesItTest {

    private static final String DATA = """
            module demo

            data A = { q: Int, p: Int }
            """;

    @Test
    void aProductInAnyIsAProductAtBothFields() {
        assertEquals(List.of("xs[*].p: NON_AFFINE_PRODUCT", "xs[*].q: NON_AFFINE_PRODUCT"),
                reasons("""
                        behavior f : (xs: List<A>) -> Bool
                        let f (xs) = List.any(i -> i.q * i.p >= 1000, xs)
                        """));
    }

    @Test
    void theSameProductCountedIsTheSameProduct() {
        assertEquals(List.of("xs: NON_AFFINE_PRODUCT", "xs[*].p: NON_AFFINE_PRODUCT",
                        "xs[*].q: NON_AFFINE_PRODUCT"),
                reasons("""
                        behavior f : (xs: List<A>) -> Bool
                        let f (xs) = List.length(List.filter(i -> i.q * i.p >= 1000, xs)) >= 1
                        """));
    }

    @Test
    void aProductNamedBeforeItIsComparedIsTheSameProduct() {
        assertEquals(List.of("xs[*].p: NON_AFFINE_PRODUCT", "xs[*].q: NON_AFFINE_PRODUCT"),
                reasons("""
                        behavior f : (xs: List<A>) -> Bool
                        let f (xs) = List.any(i -> {
                            let amount = i.q * i.p
                            amount >= 1000
                        }, xs)
                        """));
    }

    @Test
    void aProductWrittenInAHelperIsTheSameProduct() {
        assertEquals(List.of("xs: NON_AFFINE_PRODUCT", "xs[*]: NON_AFFINE_PRODUCT"),
                reasons("""
                        behavior amount : (a: A) -> Int
                        let amount (a) = a.q * a.p

                        behavior f : (xs: List<A>) -> Bool
                        let f (xs) = List.length(List.filter(i -> amount(i) >= 1000, xs)) >= 1
                        """));
    }

    /**
     * An operation whose form the library states, handed a product. The reading stops at the call,
     * which is what the author wrote, and it stopped for what stopped its argument.
     */
    @Test
    void aProductUnderAnOperationWhoseFormIsStatedIsTheSameProduct() {
        assertEquals(List.of("a: NON_AFFINE_PRODUCT", "b: NON_AFFINE_PRODUCT"),
                reasons("""
                        behavior f : (a: Int, b: Int) -> Bool
                        let f (a, b) = Int.add(a * b, 1) >= 1000
                        """));
    }

    @Test
    void aQuotientByAnInputIsADivisorAndNotAProduct() {
        assertEquals(List.of("xs[*].p: NON_CONSTANT_DIVISOR", "xs[*].q: NON_CONSTANT_DIVISOR"),
                reasons("""
                        behavior f : (xs: List<A>) -> Bool
                        let f (xs) = List.any(i -> i.q / i.p >= 10, xs)
                        """));
    }

    /**
     * Two parts of one statement that stopped for different arithmetic are not one operation, and
     * the count over them does not name either: what they have in common is a part not read. Each
     * conjunct is a comparison of its own at the element, and says what it met.
     */
    @Test
    void twoDifferentOperationsAreNeitherOfThemWhereTheyAreCountedTogether() {
        assertEquals(List.of("xs: RULE_MEANING_NOT_READ",
                        "xs[*].p: NON_AFFINE_PRODUCT", "xs[*].p: NON_CONSTANT_DIVISOR",
                        "xs[*].p: RULE_MEANING_NOT_READ",
                        "xs[*].q: NON_AFFINE_PRODUCT", "xs[*].q: NON_CONSTANT_DIVISOR",
                        "xs[*].q: RULE_MEANING_NOT_READ"),
                reasons("""
                        behavior f : (xs: List<A>) -> Bool
                        let f (xs) = List.length(List.filter(
                            i -> i.q * i.p >= 1000 && i.q / i.p >= 10, xs)) >= 1
                        """));
    }

    @Test
    void aProductBySomethingConstantIsNotOneAtAll() {
        assertFalse(reasons("""
                behavior f : (xs: List<A>) -> Bool
                let f (xs) = List.any(i -> i.q * 2 >= 1000, xs)
                """).toString().contains("NON_AFFINE_PRODUCT"));
        assertFalse(reasons("""
                behavior f : (xs: List<A>) -> Bool
                let f (xs) = List.any(i -> i.q + i.p >= 1000, xs)
                """).toString().contains("NON_AFFINE_PRODUCT"));
    }

    @Test
    void aProductBetweenTwoPositionsIsAProductAtEach() {
        assertEquals(List.of("a: NON_AFFINE_PRODUCT", "b: NON_AFFINE_PRODUCT"),
                reasons("""
                        behavior f : (a: Int, b: Int) -> Bool
                        let f (a, b) = a * b >= 1000
                        """));
    }

    /** The same arithmetic in a clause, which is read by the invariant's reader and not a body's. */
    @Test
    void aProductInAnInvariantIsAProduct() {
        String model = """
                module demo

                data Box = { w: Int, h: Int }
                    invariant w * h <= 100

                behavior f : (b: Box) -> Bool
                let f (b) = true
                """;
        assertEquals(List.of("b.h: NON_AFFINE_PRODUCT", "b.w: NON_AFFINE_PRODUCT"),
                reasonsOf(model));
    }

    /** Each position paired with the word a report is told, in a steady order. */
    private static List<String> reasons(String behaviors) {
        return reasonsOf(DATA + "\n" + behaviors);
    }

    private static List<String> reasonsOf(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, PartitionEvidence> coverage =
                compilation.db().ask(new Adequacy.Coverage("demo")).value();
        assertNotNull(coverage, () -> "the model under test compiles: " + model);
        PartitionEvidence measured = coverage.get("f");
        assertNotNull(measured, () -> "f was measured: " + model);
        return measured.notRead().stream()
                .map(each -> each.at() + ": " + each.reason())
                .distinct()
                .sorted()
                .collect(Collectors.toList());
    }
}
