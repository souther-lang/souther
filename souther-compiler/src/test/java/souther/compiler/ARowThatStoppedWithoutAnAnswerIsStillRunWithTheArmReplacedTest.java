package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.meta.ModulePath;
import souther.compiler.observe.AnswerObservation;
import souther.compiler.observe.Disposition;
import souther.compiler.observe.ReplacedRun;
import souther.compiler.observe.RowOutcome;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Output;
import souther.compiler.source.SourceId;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A row that went through an arm and stopped there without an answer is run again with the arm
 * replaced, as a row that answered is.
 *
 * <p>The arm builds a value its own invariant refuses, so the row stops inside it and fails. With
 * the arm answering as its sibling the row holds — which tells the arm from the sibling as surely
 * as two answers would, and is the row's to say rather than something left unasked because the
 * row as written answered nothing.
 */
class ARowThatStoppedWithoutAnAnswerIsStillRunWithTheArmReplacedTest {

    private static final String MODEL = """
            module example.refund

            data Amount = Int
                invariant value >= 0

            data OutOfPocket
            data Advance
            data Payer = OutOfPocket | Advance

            data Item = { amount: Amount, payer: Payer }

            behavior refund : (item: Item) -> Amount
                constructs Amount

            let refund (item) = match item.payer with
                | OutOfPocket -> Amount(item.amount.value - 1)
                | Advance     -> Amount(0)

            example refund
                | "nothing out of pocket" : (Item { amount = Amount(0), payer = OutOfPocket })
                    -> Amount(0)
            """;

    @Test
    void aRowThatStoppedInTheArmNoticesItAnsweringAsItsSibling() {
        RowOutcome row = rowNamed("nothing out of pocket");

        assertEquals(Disposition.FAILED, row.disposition(), "the arm refuses what it builds: " + row);
        assertInstanceOf(AnswerObservation.NotAnswered.class, row.answer(),
                "and the row got no answer: " + row);
        assertEquals(1, row.replaced().size(), "run again with the arm as its sibling: "
                + row.replaced());
        assertEquals(ReplacedRun.Noticed.YES, row.replaced().getFirst().noticed(),
                "and holds under it: " + row.replaced());
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
