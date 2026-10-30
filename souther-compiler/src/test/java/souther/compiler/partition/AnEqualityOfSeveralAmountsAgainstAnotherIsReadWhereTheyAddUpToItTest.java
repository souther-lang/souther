package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * An equality of the sum of several amounts with another amount is read, wherever the amounts are
 * bounded one place at a time.
 *
 * <p>No one of the amounts reaches every value the other has to stand at: the other runs over the
 * whole of what they come to, which is more than any one of them holds. They reach it together —
 * each takes every whole number of its run, so their sum takes every whole number from the least
 * to the greatest — and the equality holds at the sum and fails beside it. Left unbounded, the sum
 * can pass the greatest {@code Int} and a run stops there.
 */
class AnEqualityOfSeveralAmountsAgainstAnotherIsReadWhereTheyAddUpToItTest {

    private static final String SOURCE = """
            module demo

            data Yen = Int
                invariant value >= 0
            data Pay = { a: Yen, b: Yen, c: Yen }
                %s
            data Out = { n: Int }

            behavior f : (p: Pay, previous: Yen) -> Out
                constructs Out
            let f (p, previous) = Out { n = if %s then 1 else 0 }
            """;

    private static final String THE_SUM_EQUALS_IT = "p.a.value + p.b.value + p.c.value"
            + " == previous.value";

    private static final String BOUNDS = """
            invariant a.value <= 1000000000000
                invariant b.value <= 1000000000000
                invariant c.value <= 1000000000000""";

    /** The places the report says nothing is read of. */
    private static List<String> unread(String bounds, String relation) {
        Compilation compilation = Compilation.ofSource(SOURCE.formatted(bounds, relation), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model under test compiles");
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts())).lines()
                .filter(line -> line.contains("not read:"))
                .map(line -> line.replaceAll(".*about `([^`]*)`.*", "$1"))
                .toList();
    }

    @Test
    void anEqualityOfTheSumOfBoundedAmountsIsRead() {
        assertEquals(List.of(), unread(BOUNDS, THE_SUM_EQUALS_IT));
    }

    /** The other amount written first, so that the amounts are the ones weighed minus one. */
    @Test
    void theSameEqualityWithTheOtherAmountWrittenFirstIsRead() {
        assertEquals(List.of(), unread(BOUNDS,
                "previous.value == p.a.value + p.b.value + p.c.value"));
    }

    /** Control: with no bound the sum of three can pass the greatest {@code Int}; the run stops
     *  there and the equality is not read. */
    @Test
    void theSameEqualityOfUnboundedAmountsIsNotRead() {
        assertFalse(unread("", THE_SUM_EQUALS_IT).isEmpty());
    }
}
