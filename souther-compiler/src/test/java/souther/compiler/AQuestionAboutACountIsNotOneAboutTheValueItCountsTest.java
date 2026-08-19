package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.check.CoverageObligation;
import souther.compiler.diag.SourceNameResolver;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A line on a count is about the count, wherever the rule that draws it is written.
 *
 * <p>{@code Owed.Subject} carries the count apart from the position on purpose, and says so: which
 * of the two a question is about is settled where the question is raised and not by whatever a
 * reader downstream has to hand. That is how a line about a string's length came to be printed as a
 * fact about which strings may stand there.
 *
 * <p>Only a question nothing answered shows it. A rule this compiler can read leaves no question, so
 * a comparison whose bound cannot be folded is what these are written on — the subject is then the
 * one thing about the question a report has left to get right.
 */
class AQuestionAboutACountIsNotOneAboutTheValueItCountsTest {

    private static PartitionEvidence partitionOf(String source, String behavior) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        for (AdequacyReport.BehaviorReport each
                : AdequacyReport.of(compilation).modules().get(0).behaviors()) {
            if (each.name().equals(behavior)) {
                return each.partition();
            }
        }
        throw new AssertionError("no behavior called " + behavior);
    }

    /** The number the line question falls on, which is the only one both producers raise. */
    private static String lineSubjectIn(PartitionEvidence partition) {
        return partition.unanswered().stream()
                .filter(each -> each.question() == CoverageObligation.BOUNDARY)
                .map(PartitionEvidence.Unanswered::measure)
                .findFirst().orElseThrow(() -> new AssertionError(
                        "no line was asked about: " + partition.unanswered()));
    }

    /** A guard on a length, with a bound this cannot fold. */
    @Test
    void aGuardOnALengthAsksAboutTheLength() {
        PartitionEvidence partition = partitionOf("""
                module example.rooms

                data Code = { text: String }

                behavior price : (c: Code) -> Int
                let price (c) =
                    if String.length(c.text) <= 10 * 2 then 1 else 2

                example price
                    | "one" : (Code { text = "a" }) -> 2
                """, "price");

        assertEquals("String.length(c.text)", lineSubjectIn(partition),
                () -> "the line is on the count and the values are the string's: "
                        + partition.unanswered());
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
                    ensures TooShort -> String.length(c.text) <= 10 * 2
                let price (c) = TooShort

                example price
                    | "one" : (Code { text = "a" }) -> TooShort
                """, "price");

        assertEquals("String.length(c.text)", lineSubjectIn(partition),
                () -> "read the same way wherever the rule is written: " + partition.unanswered());
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
