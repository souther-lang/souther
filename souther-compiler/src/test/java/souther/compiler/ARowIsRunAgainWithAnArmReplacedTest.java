package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.meta.ModulePath;
import souther.compiler.observe.AnswerChange;
import souther.compiler.observe.AnswerObservation;
import souther.compiler.observe.ObservedValue;
import souther.compiler.observe.ReplacedRun;
import souther.compiler.observe.RowOutcome;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Output;
import souther.compiler.source.SourceId;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row that went through an arm is run again with each sibling the classes carry answering in that
 * arm's place, and says whether it noticed.
 *
 * <p>The shape the question comes from: one arm answers what the input holds and its siblings answer
 * a constant. A row whose input holds that same constant goes through the first arm and answers
 * exactly what either sibling would — the arm could be written as either of them and the row would
 * not notice. A row holding anything else would.
 *
 * <p>What is replaced is the arm the author wrote, and what the row is held to is what it states. A
 * row naming only the case it expects notices nothing that stays inside the case, and a row whose
 * answer is owed states nothing a replacement could fail — and the replaced answer is kept beside
 * either, because whether the replacement changed what came back is a question of its own.
 */
class ARowIsRunAgainWithAnArmReplacedTest {

    private static final String MODEL = """
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
                | "nothing out of pocket" : (Item { amount = Amount(0), payer = OutOfPocket })
                    -> Amount(0)
                | "something out of pocket" : (Item { amount = Amount(5), payer = OutOfPocket })
                    -> Amount(5)
                | "an advance" : (Item { amount = Amount(5), payer = Advance }) -> Amount(0)
                | "owed" : (Item { amount = Amount(5), payer = OutOfPocket }) -> <?>
            """;

    @Test
    void aRowWhoseAnswerEverySiblingWouldGiveNoticesNoReplacement() {
        Map<Integer, ReplacedRun> runs = replacedOf(rowNamed("nothing out of pocket"));

        assertEquals(List.of(1, 2), List.copyOf(runs.keySet()),
                "the arm it went through is replaced by each of its siblings: " + runs);
        for (ReplacedRun run : runs.values()) {
            assertEquals(ReplacedRun.Noticed.NO, run.noticed(), "the row holds either way: " + run);
            assertEquals(0, amountIn(run.answer()));
            assertEquals(AnswerChange.SAME, run.changed(),
                    "and nothing changed on this input to be noticed");
        }
    }

    @Test
    void aRowWhoseAnswerNoSiblingGivesNoticesEveryReplacement() {
        Map<Integer, ReplacedRun> runs = replacedOf(rowNamed("something out of pocket"));

        assertEquals(List.of(1, 2), List.copyOf(runs.keySet()));
        for (ReplacedRun run : runs.values()) {
            assertEquals(ReplacedRun.Noticed.YES, run.noticed(), "the row fails: " + run);
            assertEquals(0, amountIn(run.answer()), "and what came back is the sibling's answer");
            assertEquals(AnswerChange.CHANGED, run.changed());
        }
    }

    /**
     * A sibling that reads what its own arm names is one that cannot stand anywhere else, and a row
     * through an arm with no other sibling is run again for none.
     */
    @Test
    void aRowIsRunAgainOnlyForTheArmItWentThrough() {
        Map<Integer, ReplacedRun> runs = replacedOf(rowNamed("an advance"));

        assertEquals(List.of(0, 2), List.copyOf(runs.keySet()),
                "the arm it went through is the second, and the other two stand in for it: " + runs);
        assertEquals(ReplacedRun.Noticed.YES, runs.get(0).noticed(),
                "answering what the item holds is not answering nothing");
        assertEquals(ReplacedRun.Noticed.NO, runs.get(2).noticed(),
                "answering the same constant is");
        assertEquals(AnswerChange.CHANGED, runs.get(0).changed());
        assertEquals(AnswerChange.SAME, runs.get(2).changed());
    }

    @Test
    void aRowWhoseAnswerIsOwedStatesNothingAReplacementCouldFail() {
        Map<Integer, ReplacedRun> runs = replacedOf(rowNamed("owed"));

        assertEquals(List.of(1, 2), List.copyOf(runs.keySet()));
        for (ReplacedRun run : runs.values()) {
            assertEquals(ReplacedRun.Noticed.STATES_NOTHING, run.noticed());
            assertEquals(AnswerChange.CHANGED, run.changed(),
                    "a row stating nothing still shows the replacement answers differently");
            assertEquals(0, amountIn(run.answer()),
                    "and what the replacement answered is kept all the same");
        }
    }

    @Test
    void theRowsOwnOutcomeIsWhatItWasWithoutTheReplacements() {
        RowOutcome row = rowNamed("something out of pocket");

        assertEquals(5, amountIn(row.answer()));
        assertTrue(row.observed(), "the row answered as written: " + row);
    }

    /** The whole number an answer of {@code Amount} holds. */
    private static long amountIn(AnswerObservation answer) {
        ObservedValue.Constructed amount = assertInstanceOf(ObservedValue.Constructed.class,
                assertInstanceOf(AnswerObservation.Answered.class, answer).value());
        return assertInstanceOf(ObservedValue.Integer.class, amount.field("value")).value();
    }

    private static Map<Integer, ReplacedRun> replacedOf(RowOutcome row) {
        Map<Integer, ReplacedRun> byWith = new TreeMap<>();
        for (ReplacedRun run : row.replaced()) {
            byWith.put(run.with(), run);
        }
        return byWith;
    }

    private static RowOutcome rowNamed(String name) {
        Compilation compilation = Compilation.ofSources(List.of(MODEL), ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        List<RowOutcome> rows = new ArrayList<>();
        for (String module : compilation.modules()) {
            for (SourceId id : compilation.exampleSourcesOf(module)) {
                Output.Examples.Of ran = compilation.db()
                        .ask(Output.Examples.asked(compilation.db(), module, id)).value();
                if (ran != null) {
                    rows.addAll(ran.rows());
                }
            }
        }
        return rows.stream().filter(row -> row.identity().shown().equals(name)).findFirst()
                .orElseThrow(() -> new AssertionError("no row `" + name + "` in " + rows));
    }
}
