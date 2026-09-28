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
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A combination nothing is in is raised, offered a row, and answered by it.
 *
 * <p>The whole way round, which is what the account is for: the criterion says what is owed, the
 * search composes a row for it, writing that row settles it, and asking again offers nothing. A run
 * that could not reach the last of those would be one where a person pastes the block, answers it,
 * and reads a report that still names the gap — which is the state this issue is about.
 *
 * <p>Held as one test because the steps are only worth anything together. Each of them has a law of
 * its own elsewhere; what this says is that they compose.
 */
class AGapAtACombinationIsOfferedARowThatClosesItTest {

    /**
     * Two positions the body tells apart, and no meeting between them: the answer is a
     * construction, so the pair space is the criterion.
     */
    private static final String MODEL = """
            module example.round

            data Domestic
            data Overseas
            data Kind = Domestic | Overseas
            data Amount = Int
                invariant value >= 0
            data Request = { kind: Kind, cost: Amount }
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
                | (Request { kind = Domestic, cost = Amount(50) })  -> Ok { n = 0 }
                | (Request { kind = Domestic, cost = Amount(500) }) -> Waiting { n = 1 }
                | (Request { kind = Overseas, cost = Amount(50) })  -> Ok { n = 2 }
            """;

    /** The row the block offers for the one combination nothing is in, answered. */
    private static final String ANSWERED = """
                | (Request { kind = Overseas, cost = Amount(101) }) -> Ok { n = 2 }
            """;

    /**
     * The gap is raised, a row is offered for it, and writing that row takes it away.
     *
     * <p>The three rows cover three of the four combinations; what is left is an overseas request
     * over the line. The block offers a row that sits in both classes, and the same model with that
     * row answered raises nothing and is offered nothing.
     */
    @Test
    void aCombinationNoRowIsInIsRaisedOfferedAndThenGone() {
        Compilation before = measured(MODEL);

        List<String> raised = gapsOf(before);
        assertEquals(1, raised.size(), () -> "one combination is left: " + raised);
        assertTrue(raised.getFirst().contains("Overseas"), raised::getFirst);

        String block = block(before);
        assertTrue(block.contains("kind = Overseas"), () -> "a row is offered for it: " + block);
        assertTrue(block.contains("cost = Amount(101)"), () -> "and it is over the line: " + block);

        Compilation after = measured(MODEL + ANSWERED);
        assertEquals(List.of(), gapsOf(after),
                () -> "the row that was offered answers it: " + report(after));
        assertFalse(block(after).contains("kind = Overseas"),
                () -> "and nothing is offered for it a second time: " + block(after));
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
                        OfferingRequest.overTheModule("example.round")),
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
