package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.Located;
import souther.compiler.diag.Messages;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rewrite of a body no row tells apart is a gap a build is told about, and the verdict is not
 * satisfied while it stands.
 *
 * <p>The two shapes the question came from, end to end. An arm answering what the input holds and
 * siblings answering a constant, with every row holding that constant; and a sum whose rows all hold
 * nothing to sum. Both were reported satisfied with every arm reached and every class covered, and
 * both bodies could be rewritten — the arm as its sibling, the sum as the one answer the rows gave —
 * without any row failing. Rows that hold something to tell the two apart settle both.
 */
class ARewriteNoRowTellsApartRefusesTheVerdictTest {

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
            """;

    private static final String NOTHING_HELD = ARM + """
                | "out of pocket" : (Item { amount = Amount(0), payer = OutOfPocket }) -> Amount(0)
                | "an advance" : (Item { amount = Amount(0), payer = Advance }) -> Amount(0)
                | "a card" : (Item { amount = Amount(0), payer = CompanyCard }) -> Amount(0)
            """;

    private static final String SOMETHING_HELD = ARM + """
                | "out of pocket" : (Item { amount = Amount(5), payer = OutOfPocket }) -> Amount(5)
                | "an advance" : (Item { amount = Amount(5), payer = Advance }) -> Amount(0)
                | "a card" : (Item { amount = Amount(5), payer = CompanyCard }) -> Amount(0)
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
            """;

    @Test
    void anArmNoRowWouldMissAsItsSiblingIsAGapAndTheVerdictIsNotSatisfied() {
        Compilation compilation = compiled(NOTHING_HELD);

        assertTrue(rewritesUnnoticed(compilation) > 0,
                "the arm answering what the item holds, written as answering nothing: "
                        + Adequacy.accountOf(compilation.db(), "example.refund"));
        assertEquals(AdequacyReport.AdequacyStatus.NOT_SATISFIED,
                AdequacyReport.of(compilation).adequacy());
    }

    /** A build is warned at the arm, and sent to the row the two answer differently on. */
    @Test
    void aBuildIsWarnedAtTheArmAndToldWhichRowToWriteDown() {
        Compilation compilation = Compilation.ofSource(NOTHING_HELD, "Main");
        compilation.measure(Adequacy.Asked.warningsAt(Adequacy.Level.ALL));
        compilation.answerEverything();
        List<String> said = compilation.warnings().stream()
                .map(Located::diagnostic)
                .filter(d -> "E1939".equals(d.code()))
                .map(d -> Messages.render(d.said(), Locale.ENGLISH) + " | "
                        + d.notes().stream()
                                .map(n -> Messages.render(n.said(), Locale.ENGLISH)).toList())
                .toList();

        // Every row holds nothing, so none of them answers differently under the rewrite and the
        // row the hint names is one the search composed.
        assertTrue(said.stream().anyMatch(each -> each.startsWith(
                        "No row of `refund` would fail if this arm answered as another arm of its"
                                + " fork.")
                        && each.contains("Amount(")),
                () -> "what a build is told: " + said);
    }

    /** And the page says it beside the arms, with the gap under the count. */
    @Test
    void thePageSaysHowManyRewritesTheRowsTellApart() {
        Compilation compilation = compiled(NOTHING_HELD);
        String page = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));

        // Three: the arm answering what the item holds written as the arms answering nothing, which
        // are one rewrite since the two do the same, and each of those written as the first. Not
        // the body answering one value, which is asked of a body with no arm to rewrite.
        assertTrue(page.contains("replacement 0/3"), () -> "three rewrites, told apart by no row: "
                + page);
        assertTrue(page.contains("! no row would fail if an arm answered as its sibling"),
                () -> "and the arm under it: " + page);
    }

    @Test
    void rowsThatHoldSomethingTellEveryRewriteApart() {
        Compilation compilation = compiled(SOMETHING_HELD);

        assertEquals(0, rewritesUnnoticed(compilation),
                "every rewrite of the body fails some row: "
                        + Adequacy.accountOf(compilation.db(), "example.refund"));
    }

    @Test
    void aSumNoRowWouldMissAsOneAnswerIsAGap() {
        Compilation compilation = compiled(SUM + """
                    | "one of nothing" : ([Item { amount = Amount(0), kind = Travel }]) -> Sum(0)
                """);

        assertTrue(rewritesUnnoticed(compilation) > 0,
                "the sum written as the one answer the rows gave: "
                        + Adequacy.accountOf(compilation.db(), "example.total"));
        assertEquals(AdequacyReport.AdequacyStatus.NOT_SATISFIED,
                AdequacyReport.of(compilation).adequacy());
    }

    @Test
    void aSumWhoseRowsAnswerTwoValuesTellsOneAnswerApart() {
        Compilation compilation = compiled(SUM + """
                    | "one of five" : ([Item { amount = Amount(5), kind = Travel }]) -> Sum(5)
                """);

        assertEquals(0, rewritesUnnoticed(compilation),
                Adequacy.accountOf(compilation.db(), "example.total").toString());
    }

    private static long rewritesUnnoticed(Compilation compilation) {
        return Adequacy.accountOf(compilation.db(), compilation.modules().getFirst()).stream()
                .filter(each -> each.kind() == Adequacy.Kind.REWRITE_UNNOTICED)
                .count();
    }

    private static Compilation compiled(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code().toString()).toList(),
                "the model under test compiles");
        return compilation;
    }
}
