package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.meta.ModulePath;
import souther.compiler.partition.Replacement;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rewrite of a body no row tells from it is a gap where some row shows the rewrite answering
 * differently, and is met where a row's statement fails of it.
 *
 * <p>The two shapes the question came from. An arm answering what the input holds beside siblings
 * answering a constant, with every row holding that same constant: each row goes through the arm
 * and none would notice it written as a sibling. And a body with no fork, a sum, whose rows all hold
 * nothing to sum: every row answers one value, and none would notice the body written as that value.
 * Neither rewrite is shown to matter by the rows written; a row composed and run under both is what
 * shows it, and that row is what writing the answer down would notice it with.
 */
class ARewriteNoRowTellsApartIsAGapTest {

    private static final String ARM = """
            module example.refund

            data Amount = Int
                invariant value >= 0

            data OutOfPocket
            data Advance
            data CompanyCard
            data Payer = OutOfPocket | Advance | CompanyCard

            data Item = { amount: Amount, payer: Payer }

            behavior refund : (item: Item) -> Amount
                constructs Amount

            let refund (item) = match item.payer with
                | OutOfPocket -> item.amount
                | Advance     -> Amount(0)
                | CompanyCard -> Amount(0)

            example refund
                | "out of pocket" : (Item { amount = Amount(0), payer = OutOfPocket }) -> Amount(0)
                | "an advance" : (Item { amount = Amount(0), payer = Advance }) -> Amount(0)
                | "a card" : (Item { amount = Amount(0), payer = CompanyCard }) -> Amount(0)
            """;

    private static final String SUM = """
            module example.total

            data Amount = Int
                invariant value >= 0

            data Sum = Int

            data Travel
            data Lodging
            data Kind = Travel | Lodging

            data Item = { amount: Amount, kind: Kind }

            behavior total : (items: List<Item>) -> Sum
                constructs Sum

            let total (items) =
                Sum(List.fold((sum, item) -> sum + item.amount.value, 0, items))

            example total
                | "nothing" : ([]) -> Sum(0)
                | "one of nothing" : ([Item { amount = Amount(0), kind = Travel }]) -> Sum(0)
            """;

    @Test
    void anArmEveryRowGoesThroughAndNoneWouldMissIsAGap() {
        Map<Replacement, ReplacementEvidence.Outcome> rewrites = rewritesOf(ARM, "refund");

        ReplacementEvidence.Outcome asAdvance = rewrites.entrySet().stream()
                .filter(each -> each.getKey() instanceof Replacement.OfAnArm(var _, var part,
                        var with) && part == 0 && with == 1)
                .map(Map.Entry::getValue).findFirst()
                .orElseThrow(() -> new AssertionError("the first arm as the second: " + rewrites));
        ReplacementEvidence.Unnoticed gap =
                assertInstanceOf(ReplacementEvidence.Unnoticed.class, asAdvance,
                        "no row tells the arm from its sibling, and a row shows they differ: "
                                + asAdvance);
        ReplacementEvidence.ShownBy.AComposedRow shown = assertInstanceOf(
                ReplacementEvidence.ShownBy.AComposedRow.class, gap.shownBy(),
                "no written row shows it, so the row that does was composed");
        assertFalse(shown.inputs().getFirst().contains("Amount(0)"),
                "and it holds something out of pocket: " + shown.inputs());
    }

    /** Two arms that do the same thing are one arm written twice, and neither is a rewrite of the
     *  other: no row could tell them apart, so nothing is owed for it either way. */
    @Test
    void siblingsThatDoTheSameThingAreNoRewriteOfEachOther() {
        Map<Replacement, ReplacementEvidence.Outcome> rewrites = rewritesOf(ARM, "refund");

        assertTrue(rewrites.keySet().stream().noneMatch(each ->
                        each instanceof Replacement.OfAnArm(var _, var part, var with)
                                && ((part == 1 && with == 2) || (part == 2 && with == 1))),
                "the two arms answering one constant are not rewrites of each other: " + rewrites);
    }

    @Test
    void aBodyEveryRowAnswersAlikeIsAGap() {
        Map<Replacement, ReplacementEvidence.Outcome> rewrites = rewritesOf(SUM, "total");

        List<ReplacementEvidence.Outcome> oneAnswer = oneAnswers(rewrites);
        assertEquals(1, oneAnswer.size(), "every row answers one value: " + rewrites);
        ReplacementEvidence.Unnoticed gap =
                assertInstanceOf(ReplacementEvidence.Unnoticed.class, oneAnswer.getFirst(),
                        "every row answers the same, and a row shows the body does not always: "
                                + rewrites);
        assertTrue(gap.shownBy() instanceof ReplacementEvidence.ShownBy.AComposedRow,
                "shown by a composed row: " + gap.shownBy());
    }

    /** Two values, two rewrites, and each told apart by the row answering the other. */
    @Test
    void aBodyTwoRowsAnswerDifferentlyIsNoticedOncePerValue() {
        String told = SUM.replace(
                "| \"one of nothing\" : ([Item { amount = Amount(0), kind = Travel }]) -> Sum(0)",
                "| \"one of five\" : ([Item { amount = Amount(5), kind = Travel }]) -> Sum(5)");

        List<ReplacementEvidence.Outcome> oneAnswer = oneAnswers(rewritesOf(told, "total"));

        assertEquals(2, oneAnswer.size(), "a rewrite per value: " + oneAnswer);
        assertTrue(oneAnswer.stream().allMatch(ReplacementEvidence.Noticed.class::isInstance),
                "each told apart: " + oneAnswer);
    }

    /**
     * Rows that name only the case leave every value a rewrite could answer standing, and each is
     * a rewrite of its own: answering what the first row came to and answering what the second
     * came to are two programs, and a row telling one apart says nothing of the other.
     */
    @Test
    void rowsNamingOnlyTheCaseLeaveARewritePerValue() {
        List<ReplacementEvidence.Outcome> oneAnswer = oneAnswers(rewritesOf("""
                module example.cases

                data Ok = { n: Int }
                data Err
                data Result = Ok | Err

                behavior f : (x: Int) -> Result
                    constructs Ok

                let f (x) = Ok { n = x }

                example f
                    | "nought" : (0) -> Ok
                    | "one" : (1) -> Ok
                """, "f"));

        assertEquals(2, oneAnswer.size(), "a rewrite per value the rows came to: " + oneAnswer);
        assertTrue(oneAnswer.stream().allMatch(ReplacementEvidence.Unnoticed.class::isInstance),
                "neither told apart, and each shown to differ: " + oneAnswer);
    }

    /**
     * A body reading nothing answers one value already, and that value is no rewrite of it: the
     * rows are owed nothing for it however they are written.
     */
    @Test
    void aBodyThatReadsNothingIsNoRewriteOfItsOwnAnswer() {
        Map<Replacement, ReplacementEvidence.Outcome> rewrites = rewritesOf("""
                module example.flat

                data Ok = { n: Int }

                behavior cancel : (x: Int) -> Ok
                    constructs Ok

                let cancel (x) = Ok { n = 1 }

                example cancel
                    | (0) -> Ok { n = 1 }
                    | (5) -> Ok { n = 1 }
                """, "cancel");

        assertEquals(Map.of(), rewrites, "nothing to rewrite: " + rewrites);
    }

    /**
     * A body answering what a dependency answers reads no name, and is not one value for that: the
     * dependency's answer arrives as a call, and each row stands it in with a value of its own.
     * Answering either row's value always is a rewrite of the body, told apart by the other row.
     */
    @Test
    void aBodyAnsweringWhatADependencyAnswersIsNotOneValue() {
        List<ReplacementEvidence.Outcome> oneAnswer = oneAnswers(rewritesOf("""
                module example.filing

                data Stamp = String
                data Filed = { at: Stamp }

                behavior now : () -> Stamp

                behavior file : (at: Stamp) -> Filed
                    constructs Filed
                    depends on now

                let file (at, now) = Filed { at = now() }

                example file
                    | "ten" : (Stamp("x"))
                        with now = Stamp("10:00")
                        -> Filed { at = Stamp("10:00") }
                    | "nine" : (Stamp("x"))
                        with now = Stamp("09:00")
                        -> Filed { at = Stamp("09:00") }
                """, "file"));

        assertEquals(2, oneAnswer.size(), "a rewrite per value the rows came to: " + oneAnswer);
        assertTrue(oneAnswer.stream().allMatch(ReplacementEvidence.Noticed.class::isInstance),
                "each told apart by the other row: " + oneAnswer);
    }

    /** The rewrites of a body answering one value, in the order the values were first answered. */
    private static List<ReplacementEvidence.Outcome> oneAnswers(
            Map<Replacement, ReplacementEvidence.Outcome> rewrites) {
        List<ReplacementEvidence.Outcome> out = new ArrayList<>();
        rewrites.forEach((rewrite, outcome) -> {
            if (rewrite instanceof Replacement.ByOneAnswer) {
                out.add(outcome);
            }
        });
        return out;
    }

    private static Map<Replacement, ReplacementEvidence.Outcome> rewritesOf(String source,
                                                                            String behavior) {
        Compilation compilation = Compilation.ofSources(List.of(source), ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code()).toList(),
                "the model under test compiles");
        String module = compilation.modules().get(0);
        Map<String, ReplacementEvidence> measured =
                compilation.db().ask(new Replacements.Measured(module)).value();
        ReplacementEvidence its = measured.get(behavior);
        Map<Replacement, ReplacementEvidence.Outcome> out = new LinkedHashMap<>();
        its.measured().made().orElseThrow(() -> new AssertionError(
                        "the rewrites were measured: " + its.measured()))
                .rewrites().forEach(each -> out.put(each.replacement(), each.outcome()));
        return out;
    }
}
