package souther.compiler;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;
import souther.compiler.diag.SourceRendering;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A combination the model refuses the baseline at is reached by moving the rest of the row.
 *
 * <p>What a combination of two classes names is two positions and their classes. Everything else
 * about a row is free — and where the model relates a free position to a pinned one, the values the
 * search started from stop being a value the model admits as soon as the pins are taken. The way
 * through is to move the free position, which is the one the requirement says nothing about.
 *
 * <p><b>Never by giving a pin up.</b> The other way out of a refused candidate is to loosen one of
 * the two classes, and it produces a row the search can call an answer while the combination it was
 * asked for is still one nothing sits in. A person pastes it, reads the same gap again, and has no
 * way to tell that from the model having no such row.
 */
class ACombinationIsReachedByMovingWhatItSaysNothingAboutTest {

    /**
     * The cap is free and the cost is pinned, and the model relates them.
     *
     * <p>The body tells two positions apart — the case of the request and which side of the line
     * its cost falls — and decides nothing about the cap. So the cap is not a position the
     * combinations are over, while the invariant makes every row's cap a value the cost settles.
     */
    private static final String MODEL = """
            module example.repair

            data Domestic
            data Overseas
            data Kind = Domestic | Overseas
            data Amount = Int
                invariant value >= 0
            data Request = { kind: Kind, cost: Amount, cap: Amount }
                invariant within = cost.value <= cap.value
            data Ok = { n: Int }
            data Waiting = { n: Int }

            behavior submit : (request: Request) -> Ok | Waiting
                constructs Ok, Waiting

            let submit (request) = match request.kind with
                | Domestic -> {
                    guard request.cost.value <= 100 else Waiting { n = 1 }
                    Ok { n = 0 }
                }
                | Overseas -> Ok { n = 2 }

            example submit
                | (Request { kind = Domestic, cost = Amount(50), cap = Amount(50) }) -> Ok { n = 0 }
            """;

    /**
     * Every combination is offered a row, and the rows carry the classes they were asked for.
     *
     * <p>A cost over the line needs a cap over it too, and the search moves the cap rather than
     * the cost. Answered by loosening the pin instead, the block would hold a row under the line
     * at a combination asked for above it.
     */
    @Test
    void aRowIsOfferedAtTheCombinationAndItIsTheCombinationThatWasAskedFor() {
        Compilation before = measured(MODEL);
        List<String> raised = gapsOf(before);
        assertTrue(raised.size() > 1, () -> "combinations are left here: " + raised);

        String block = block(before);
        assertTrue(block.contains("cost = Amount(101)"),
                () -> "a row is offered over the line: " + block);
        assertTrue(block.contains("cap = Amount(101)"),
                () -> "and the cap moved to where the model admits it: " + block);

        String answered = MODEL + rowsOf(block);
        Compilation after = measured(answered);
        assertEquals(List.of(), after.errors(),
                () -> "the rows offered are rows this model admits:\n" + answered);
        assertEquals(List.of(), gapsOf(after),
                () -> "and they answer every combination: " + report(after));
    }

    /** The rows of an offered block, as a person pastes them under the example already written. */
    private static String rowsOf(String block) {
        List<String> rows = block.lines()
                .filter(each -> each.strip().startsWith("| (Request"))
                .map(each -> "    " + each.strip())
                .toList();
        assertTrue(rows.size() > 1, () -> "the block offers rows: " + block);
        return String.join("\n", rows) + "\n";
    }

    /** What a strict build refuses over here, in the words the report writes. */
    private static List<String> gapsOf(Compilation compilation) {
        return AdequacyReport.of(compilation).adequacyGaps().stream()
                .filter(each -> each.kind() == Adequacy.Kind.PAIR_UNCOVERED)
                .map(each -> each.about().toString())
                .toList();
    }

    private static String block(Compilation compilation) {
        return GeneratedRows.of(
                Adequacy.offeredFor(compilation.db(),
                        OfferingRequest.overTheModule("example.repair")),
                Map.of(), SourceRendering.namedByIdentity(compilation.texts()),
                compilation.db()).text();
    }

    private static String report(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }
}
