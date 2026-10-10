package souther.compiler.partition;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import org.junit.jupiter.api.Test;

import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * Arithmetic no form says is reported as the arithmetic it was, whichever way the comparison reaches
 * the position: compared directly, handed to an operation over a container, counted, named, or
 * written in a helper.
 *
 * <p>The arithmetic decides which operation it met, where it composes the operands. What a report
 * says is that decision carried through, so a closure around the product changes nothing about it,
 * and nothing is asked of where the value came from to say it again.
 */
class AProductOfTwoInputsIsReportedAsAProductWhateverCarriesItTest {

    private static final String DATA = """
            module demo

            data A = { q: Int, p: Int }
            """;

    @Test
    void aProductInAnyIsAProduct() {
        assertEquals(Set.of(UndividedPosition.Reason.NON_AFFINE_PRODUCT), reasons("""
                behavior f : (xs: List<A>) -> Bool
                let f (xs) = List.any(i -> i.q * i.p >= 1000, xs)
                """));
    }

    @Test
    void theSameProductCountedIsTheSameProduct() {
        assertEquals(Set.of(UndividedPosition.Reason.NON_AFFINE_PRODUCT), reasons("""
                behavior f : (xs: List<A>) -> Bool
                let f (xs) = List.length(List.filter(i -> i.q * i.p >= 1000, xs)) >= 1
                """));
    }

    @Test
    void aProductNamedBeforeItIsComparedIsTheSameProduct() {
        assertEquals(Set.of(UndividedPosition.Reason.NON_AFFINE_PRODUCT), reasons("""
                behavior f : (xs: List<A>) -> Bool
                let f (xs) = List.any(i -> {
                    let amount = i.q * i.p
                    amount >= 1000
                }, xs)
                """));
    }

    @Test
    void aProductWrittenInAHelperIsTheSameProduct() {
        assertEquals(Set.of(UndividedPosition.Reason.NON_AFFINE_PRODUCT), reasons("""
                behavior amount : (a: A) -> Int
                let amount (a) = a.q * a.p

                behavior f : (xs: List<A>) -> Bool
                let f (xs) = List.length(List.filter(i -> amount(i) >= 1000, xs)) >= 1
                """));
    }

    @Test
    void aQuotientByAnInputIsADivisorAndNotAProduct() {
        assertEquals(Set.of(UndividedPosition.Reason.NON_CONSTANT_DIVISOR), reasons("""
                behavior f : (xs: List<A>) -> Bool
                let f (xs) = List.any(i -> i.q / i.p >= 10, xs)
                """));
    }

    @Test
    void aProductBySomethingConstantIsNotOneAtAll() {
        assertFalse(reasons("""
                behavior f : (xs: List<A>) -> Bool
                let f (xs) = List.any(i -> i.q * 2 >= 1000, xs)
                """).contains(UndividedPosition.Reason.NON_AFFINE_PRODUCT));
        assertFalse(reasons("""
                behavior f : (xs: List<A>) -> Bool
                let f (xs) = List.any(i -> i.q + i.p >= 1000, xs)
                """).contains(UndividedPosition.Reason.NON_AFFINE_PRODUCT));
    }

    @Test
    void aProductBetweenTwoPositionsIsAProductToo() {
        assertEquals(Set.of(UndividedPosition.Reason.NON_AFFINE_PRODUCT), reasons("""
                behavior f : (a: Int, b: Int) -> Bool
                let f (a, b) = a * b >= 1000
                """));
    }

    /** Every reason a report is told stopped the reading of {@code behaviors}, over {@code DATA}. */
    private static Set<UndividedPosition.Reason> reasons(String behaviors) {
        String model = DATA + "\n" + behaviors;
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, PartitionEvidence> coverage =
                compilation.db().ask(new Adequacy.Coverage("demo")).value();
        assertNotNull(coverage, () -> "the model under test compiles: " + model);
        PartitionEvidence measured = coverage.get("f");
        assertNotNull(measured, () -> "f was measured: " + model);
        return measured.notRead().stream()
                .map(PartitionEvidence.NotRead::reason)
                .collect(Collectors.toSet());
    }
}
