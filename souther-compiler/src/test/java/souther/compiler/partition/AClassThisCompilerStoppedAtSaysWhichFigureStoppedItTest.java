package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A class this compiler stopped before reaching a value for names what stopped it, so a reader is
 * told whether there is a number they could raise.
 *
 * <p>A class already says that it did not reach a value and that this does not make one unwritable.
 * What it did not say is which figure of this compiler's ended the reaching — the figures were read
 * to choose that word and dropped — so an author was told there was work to do with nothing in it
 * they could do. A point of a border in the same run does say it, which is the vocabulary this
 * joins rather than a second one.
 *
 * <p>Written from what a reader does about the answer rather than from the cases the recipe has.
 * There are two things to do and they are not alike: raise a number, or wait for somebody to write
 * the rest of what this compiler walks. So the check is that a class stopped at a figure names one,
 * and that a class nothing of this compiler's stopped names none — an opening that appeared
 * everywhere would tell an author to raise something wherever no row was written.
 */
class AClassThisCompilerStoppedAtSaysWhichFigureStoppedItTest {

    /**
     * A class of counts higher than the position holds any of.
     *
     * <p>A set of truths holds two at most, so the counts this class admits run past what this
     * compiler tries and none of the ones it tried built. Which is this compiler giving up at a
     * figure, and the figure is one somebody can raise.
     */
    private static final String MORE_THAN_IT_HOLDS = """
            module example.stopped

            behavior h : (s: Set<Bool>) -> Bool
            let h (s) = {
                guard Set.size(s) >= 3 else false

                true
            }
            """;

    /**
     * A class the rules leave nothing in, which no figure of this compiler's is why.
     *
     * <p>The control, and it has to be a class no row is written for as well — a model that simply
     * composes would say nothing either way. Here the month is narrowed to February and the day is
     * asked to be the thirtieth, which is a day February has none of: the calendar is walked whole,
     * so the search looked everywhere there was and came back empty.
     */
    private static final String NOTHING_STANDS_THERE = """
            module example.stopped

            data Slot = { on: Date }

            behavior g : (slot: Slot) -> Bool
            let g (slot) = {
                guard Date.month(slot.on) >= 2 else false
                guard Date.month(slot.on) <= 2 else false
                guard Date.day(slot.on) >= 30 else false

                true
            }
            """;

    /** The figure is named, in the words this compiler names a figure to a reader in. */
    @Test
    void aClassStoppedAtAFigureNamesTheFigure() {
        String block = offered(MORE_THAN_IT_HOLDS, "h");

        assertTrue(block.contains(
                        "this compiler stopped at how many of the numbers a class admits are tried"),
                block);
    }

    /** And the word the search came back with is still there, after what stopped it. */
    @Test
    void theWordTheSearchCameBackWithIsSaidAfterTheFigure() {
        String block = offered(MORE_THAN_IT_HOLDS, "h");

        assertTrue(block.contains("are tried: nothing here composed a value whose Set.size is in"
                + " this range, which does not make one unwritable"), block);
    }

    /** And a class nothing of this compiler's stopped names nothing to raise. */
    @Test
    void aClassNothingStoppedNamesNoFigure() {
        String block = offered(NOTHING_STANDS_THERE, "g");

        assertFalse(block.contains("this compiler stopped at"), block);
        assertTrue(block.contains("no row for"), block);
    }

    /** The rows this compiler offers for what nothing covers, and the sentences beside them. */
    private static String offered(String source, String behavior) {
        Compilation compilation = measured(source);
        return souther.compiler.report.GeneratedRows.of(compilation, "example.stopped", behavior,
                SourceRendering.namedByIdentity(compilation.texts())).text();
    }

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }
}
