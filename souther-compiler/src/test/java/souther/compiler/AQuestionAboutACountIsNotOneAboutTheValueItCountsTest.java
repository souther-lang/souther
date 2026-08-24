package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A line on a count is about the count, wherever the rule that draws it is written.
 *
 * <p>The count is carried apart from the position on purpose, and which of the two a reading was
 * after is settled where the reading was, not by whatever a reader downstream has to hand. That is
 * how a line about a string's length came to be printed as a fact about which strings may stand
 * there.
 *
 * <p>A comparison whose bound cannot be folded is what these are written on, because a rule this
 * compiler reads leaves nothing standing at all. What such a rule would have divided is the part
 * that was not read — so nothing is raised about it — and the number it was read for is the one
 * thing about it a report has left to get right.
 */
class AQuestionAboutACountIsNotOneAboutTheValueItCountsTest {

    private static PartitionEvidence partitionOf(String source, String behavior) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        for (AdequacyReport.BehaviorReport each
                : AdequacyReport.of(compilation).modules().get(0).behaviors()) {
            if (each.name().equals(behavior)) {
                return each.partition();
            }
        }
        throw new AssertionError("no behavior called " + behavior);
    }

    /**
     * The number the rule was read for, which is the only one both producers name.
     *
     * <p>Off what the reading left rather than off a question it raised. A comparison this could
     * not read raises nothing — what it would have divided is the part that was not read — and
     * which number of the position it was after is still known and still the whole point: a bound
     * on the length is not a bound on which strings may stand there.
     */
    private static List<String> readFor(PartitionEvidence partition) {
        return partition.notRead().stream().map(PartitionEvidence.NotRead::at).toList();
    }

    /** A guard on a length, with a bound this cannot fold. */
    @Test
    void aGuardOnALengthAsksAboutTheLength() {
        PartitionEvidence partition = partitionOf("""
                module example.rooms

                data Code = { text: String }

                behavior price : (c: Code) -> Int
                let price (c) =
                    if String.length(c.text) <= Int.min(20, 30) then 1 else 2

                example price
                    | "one" : (Code { text = "a" }) -> 2
                """, "price");

        assertEquals(List.of("count of c.text"), readFor(partition),
                () -> "the rule was read for the count and not for the string's own values: "
                        + partition.notRead());
    }

    /** And a clause of an `ensures` on the same shape, which is the other producer. */
    @Test
    void anEnsuresOnALengthAsksAboutTheLength() {
        PartitionEvidence partition = partitionOf("""
                module example.rooms

                data Code = { text: String }
                data Ok = { at: Int }
                data TooShort

                behavior price : (c: Code) -> Ok | TooShort
                    constructs Ok
                    ensures TooShort -> String.length(c.text) <= Int.min(20, 30)
                let price (c) = TooShort

                example price
                    | "one" : (Code { text = "a" }) -> TooShort
                """, "price");

        assertEquals(List.of("count of c.text"), readFor(partition),
                () -> "read the same way wherever the rule is written: " + partition.notRead());
    }

    /**
     * A comparison against the answer raises nothing, which is not a reading falling short.
     *
     * <p>{@code value.sku == item.sku} is read and understood and draws no line a row can be written
     * at: what a row chooses is what the behavior is applied to. Raising a question about it would
     * report a model this compiler read perfectly as one it could not — the same fabrication as a
     * bound read off a rule that relates two positions.
     */
    @Test
    void aComparisonAgainstTheAnswerRaisesNothing() {
        PartitionEvidence partition = partitionOf("""
                module example.rooms

                data Item = { sku: String }
                data Line = { sku: String }

                behavior pick : (item: Item) -> Line
                    constructs Line
                    ensures Line -> value.sku == item.sku
                let pick (item) = Line { sku = item.sku }

                example pick
                    | "one" : (Item { sku = "a" }) -> Line { sku = "a" }
                """, "pick");

        assertEquals(java.util.List.of(), partition.unanswered(),
                "nothing was left standing by a rule this read to the end");
    }
}
