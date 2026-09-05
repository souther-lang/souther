package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.RunSensitivity;
import souther.compiler.partition.ReadingGap;
import souther.compiler.publish.WeakeningWord;
import souther.compiler.query.Weakening;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Every reason a reading of a border came to no number reaches the report as a sentence of its own.
 *
 * <p>The reading tells a value an observation stopped from a position the walk never reached and
 * from a row that never came, and carries which it was through the quantity, the point and the
 * weakening. What it is carried <em>for</em> is that a reader is told which one happened; a
 * projection answering one sentence for two takes the difference out at the last step, and
 * everything upstream of it becomes a distinction nobody can see.
 *
 * <p><b>The sentence, and not the word.</b> {@link WeakeningWord} sorts documents by how they are
 * weakened, and reasons that weaken one the same way are one word there on purpose. That is an
 * abstraction rather than a loss, and what makes it one is that the reason itself travels underneath
 * and is what the sentence is written from — so the census is over sentences, and what it asks of
 * the words is only that reasons sharing one weaken alike.
 *
 * <p><b>Over the cases and not over a list somebody wrote.</b> The reasons are asked of the sealed
 * type, so a reason added to {@link ReadingGap} arrives here as a case with no sentence rather than
 * as one it quietly shares — which is how two of them arrived.
 */
class EveryReasonAReadingMetIsSaidByAWordOfItsOwnTest {

    /**
     * As many sentences as there are reasons, and no two reasons under one sentence.
     *
     * <p>Both halves. Equal counts alone pass for a writer that says one sentence twice and another
     * never, and distinctness alone passes for one that leaves a reason out.
     */
    @Test
    void eachReasonHasASentenceAndNoTwoShareOne() {
        List<ReadingGap> reasons = everyReason();
        Set<String> said = new LinkedHashSet<>();
        for (ReadingGap each : reasons) {
            said.add(AdequacyReport.atTheBorder(each));
        }

        assertEquals(reasons.size(), said.size(),
                () -> "two reasons a reading met came out as one sentence: " + reasons + " to "
                        + said);
    }

    /**
     * And reasons that come out as one word weaken a document the same way.
     *
     * <p>Which is the condition the folding is allowed under, asked of the reasons rather than
     * remembered. Whether a wider run would have got a number is the whole of what a reader weighing
     * the document does with one of these, so two reasons that answer it differently are two words —
     * and the day one of the pair here comes to answer it differently, this is what says so.
     */
    @Test
    void reasonsUnderOneWordAreWeakenedAlike() {
        Map<WeakeningWord, Set<RunSensitivity>> under = new LinkedHashMap<>();
        for (ReadingGap each : everyReason()) {
            under.computeIfAbsent(wordFor(each), _ -> new LinkedHashSet<>())
                    .add(each.runSensitivity());
        }

        for (Map.Entry<WeakeningWord, Set<RunSensitivity>> each : under.entrySet()) {
            assertEquals(1, each.getValue().size(),
                    () -> "one word over reasons a wider run does not treat alike: "
                            + each.getKey() + " over " + each.getValue());
        }
    }

    private static WeakeningWord wordFor(ReadingGap why) {
        return AdequacyReport.wordFor(new Weakening.BorderValueUnreadable(null, why));
    }

    /**
     * One of each, taken from what the type permits rather than from what a reader remembers.
     *
     * <p>An observation carries a code, and the codes an observation of a value can meet are the
     * two it can meet — the rest of {@link Incompleteness.Code} is about rows and modules and
     * reaches no border. They are one reason here all the same: what the sentence says is that an
     * observation stopped, and which one it met is said under it.
     */
    private static List<ReadingGap> everyReason() {
        List<ReadingGap> out = new ArrayList<>();
        for (Class<?> permitted : ReadingGap.class.getPermittedSubclasses()) {
            out.add(switch (permitted.getSimpleName()) {
                case "Observation" -> ReadingGap.of(Incompleteness.Code.VALUE_TRUNCATED);
                case "NoValue" -> ReadingGap.NO_VALUE;
                case "CouldNotWalk" -> ReadingGap.COULD_NOT_WALK;
                case "CouldNotReadRow" -> ReadingGap.COULD_NOT_READ_ROW;
                // A reason added to the type and not to this list. Written as a failure rather than
                // skipped: a reason nothing here can build is one nothing here is checking.
                default -> throw new IllegalStateException(
                        "a reason a reading can meet that this test cannot make: " + permitted);
            });
        }
        return out;
    }
}
