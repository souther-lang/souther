package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Where a rule is filed is the quantity's answer where the reading reached one.
 *
 * <p>A rule that was read is about the quantity it cuts, so a position the arithmetic cancelled is
 * not one it says anything about. {@code a + b - b + c <= 10} is {@code a + c <= 10}: filed at
 * {@code b} as well, the report says the rule relates a position it does not mention, which is the
 * geometry coming off the canonical form while the note comes off the spelling.
 *
 * <p>Where the reading stopped there is no quantity to be about, and the positions the walk met are
 * the whole of what can be said — which is why the two are separate answers rather than one helper
 * both producers reach for.
 */
class ARuleIsFiledAtWhatItIsAboutTest {

    private static PartitionEvidence measured(String clause) {
        Compilation compilation = Compilation.ofSource("""
                module m

                data Ok = { n: Int }

                behavior f : (a: Int, b: Int, c: Int) -> Ok
                    constructs Ok
                    ensures %s
                let f (a, b, c) = Ok { n = a }

                example f
                    | "one" : (1, 2, 3) -> Ok { n = 1 }
                """.formatted(clause), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation).modules().get(0).behaviors().get(0).partition();
    }

    private static List<String> filedAt(String clause) {
        return measured(clause).notRead().stream()
                .map(PartitionEvidence.NotRead::at).sorted().toList();
    }

    /** The same over a list, for the rules whose quantity has a range of its own. */
    private static PartitionEvidence overAList(String clause) {
        Compilation compilation = Compilation.ofSource("""
                module m

                data Ok = { n: Int }

                behavior f : (xs: List<Int>, b: Int) -> Ok
                    constructs Ok
                    ensures %s
                let f (xs, b) = Ok { n = b }

                example f
                    | "one" : ([1], 2) -> Ok { n = 2 }
                """.formatted(clause), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation).modules().get(0).behaviors().get(0).partition();
    }

    /** A position the arithmetic cancels is not one the rule that was read is filed at. */
    @Test
    void aRuleThatWasReadIsFiledAtTheQuantityItCuts() {
        assertEquals(List.of("a", "c"), filedAt("a + b - b + c <= 10"),
                "the rule is `a + c <= 10`, and it says nothing about `b`");
    }

    /**
     * And one whose line the quantity never reaches is filed the same way, and says so.
     *
     * <p>A length is never negative, so {@code List.length(xs) + b - b <= -1} is read in full, its
     * quantity is found, and its line falls outside what that quantity ever holds. What it is about
     * is the length and nothing else: {@code b} is written into the clause and cancels, and a note
     * at {@code b} would say the rule states something about a position it does not mention.
     */
    @Test
    void andSoIsOneWhoseLineTheQuantityNeverReaches() {
        PartitionEvidence measured = overAList("List.length(xs) + b - b <= -1");

        assertEquals(List.of("List.length(xs)"),
                measured.notRead().stream().map(PartitionEvidence.NotRead::at).toList(),
                "the quantity is the length, and the position that cancels is not part of it");
        assertEquals(List.of(UndividedPosition.Reason.RULE_CUTS_OUTSIDE_WHAT_THE_QUANTITY_HOLDS),
                measured.notRead().stream().map(PartitionEvidence.NotRead::reason).toList(),
                "read to the end, and the line is outside where a length goes");
    }

    /**
     * A reading that stopped is filed at the positions the walk met, which may include one the
     * arithmetic would have cancelled.
     *
     * <p>Nothing is being claimed about the rule there. What it divides is the part that was not
     * read, so the walk's positions are a place to look and never a statement about the model.
     */
    @Test
    void aReadingThatStoppedIsFiledAtWhatTheWalkMet() {
        assertEquals(List.of("a", "b"), filedAt("Int.multiply(a, a) + b - b <= 9"),
                "the product stopped the reading, so `b` is where the walk looked");
    }
}
