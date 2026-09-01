package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.observe.Incompleteness;
import souther.compiler.partition.ReadingGap;
import souther.compiler.query.Weakening;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Every reason a reading of a border came to no number reaches the report as a word of its own.
 *
 * <p>The reading tells a value an observation stopped from a place the walk never reached, and
 * carries the pair through the quantity, the point and the weakening. What it is carried <em>for</em>
 * is that a reader is told which one happened; a projection answering one word for both takes the
 * difference out at the last step, and everything upstream of it becomes a distinction nobody can
 * see.
 *
 * <p><b>Over the cases and not over a list somebody wrote.</b> The reasons are asked of the sealed
 * type, so a reason added to {@link ReadingGap} arrives here as a case with no word rather than as a
 * word it quietly shares — which is how the last one arrived. What the words are is not this test's
 * to say; that they are as many as the reasons is.
 */
class EveryReasonAReadingMetIsSaidByAWordOfItsOwnTest {

    /**
     * As many words as there are reasons, and no two reasons under one word.
     *
     * <p>Both halves. Equal counts alone pass for a projection that answers one word twice and
     * another never, and distinctness alone passes for one that leaves a reason out.
     */
    @Test
    void eachReasonHasAWordAndNoTwoShareOne() {
        List<ReadingGap> reasons = everyReason();
        Set<WeakeningWord> words = new LinkedHashSet<>();
        for (ReadingGap each : reasons) {
            words.add(AdequacyReport.wordFor(new Weakening.BorderValueUnreadable(null, each)));
        }

        assertEquals(reasons.size(), words.size(),
                () -> "two reasons a reading met came out as one word: " + reasons + " to " + words);
    }

    /**
     * One of each, taken from what the type permits rather than from what a reader remembers.
     *
     * <p>An observation carries a code, and the codes an observation of a value can meet are the
     * two it can meet — the rest of {@link Incompleteness.Code} is about rows and modules and
     * reaches no border. They are one reason here all the same: what the word says is that an
     * observation stopped, and which one it met is said under it.
     */
    private static List<ReadingGap> everyReason() {
        List<ReadingGap> out = new ArrayList<>();
        for (Class<?> permitted : ReadingGap.class.getPermittedSubclasses()) {
            out.add(switch (permitted.getSimpleName()) {
                case "Observation" -> ReadingGap.of(Incompleteness.Code.VALUE_TRUNCATED);
                case "NoValue" -> ReadingGap.NO_VALUE;
                // A reason added to the type and not to this list. Written as a failure rather than
                // skipped: a reason nothing here can build is one nothing here is checking.
                default -> throw new IllegalStateException(
                        "a reason a reading can meet that this test cannot make: " + permitted);
            });
        }
        return out;
    }
}
