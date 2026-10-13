package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.meta.ModulePath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The ways an element may meet one statement are walked once for the input, however many questions
 * reach the statement.
 *
 * <p>Which ways an element can take through a choice is settled by the choice and by what the
 * declarations leave every element, and both are the input's. The statement is asked wherever a
 * condition naming it is read — by each reader of a way through, under each condition beside it — and
 * every one of those asks starts afresh. So the walk is kept with the input's reading, and the
 * readers after the first are handed what it found.
 *
 * <p>Held by counting walks rather than by timing them, as a comparison of two models over the same
 * input: the second writes the same statement under three conditions rather than one. Where each
 * question walks for itself the second walks more often; where the walk is kept, the two walk alike.
 */
class TheWaysOfOneStatementAreWalkedOnceForTheInputTest {

    private static final String THE_INPUT = """
            module q

            data Yes
            data No
            data Answer = Yes | No

            behavior f : (on: Int, xs: List<Int>) -> Answer
            """;

    private static final String STATEMENT =
            "List.any(x -> (x <= 1 || x >= 10) && (x <= 2 || x >= 20), xs)";

    private static final String ONCE = THE_INPUT
            + "let f (on, xs) = if " + STATEMENT + " then Yes else No\n";

    private static final String THREE_TIMES = THE_INPUT
            + "let f (on, xs) =\n"
            + "    if on > 1 && " + STATEMENT + " then Yes\n"
            + "    else if on > 2 && " + STATEMENT + " then Yes\n"
            + "    else if " + STATEMENT + " then Yes\n"
            + "    else No\n";

    @Test
    void oneStatementUnderMoreConditionsIsWalkedNoMoreTimes() {
        long once = walksMadeCompiling(ONCE);
        long threeTimes = walksMadeCompiling(THREE_TIMES);

        assertTrue(once > 0, "the statement was never walked, so this measures nothing");
        assertEquals(once, threeTimes,
                () -> "the statement written under three conditions was walked " + threeTimes
                        + " times against " + once + ", so a question reaching it is walking it"
                        + " again rather than being handed the ways the input's reading found");
    }

    private static long walksMadeCompiling(String source) {
        long before = DemandReading.walksMade();
        Compilation compilation = Compilation.ofSources(List.of(source), ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertTrue(compilation.diagnostics().values().stream().allMatch(List::isEmpty),
                () -> "the model under test compiles clean: " + compilation.diagnostics());
        Adequacy.offeredFor(compilation.db(),
                OfferingRequest.overTheModule(compilation.modules().get(0)));
        return DemandReading.walksMade() - before;
    }
}
