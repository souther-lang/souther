package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Two searches that came back with one word are one answer, and what each of them met of this
 * compiler's is added up under it.
 *
 * <p>The two halves of what a search came to join differently. A word is what makes two answers one
 * answer: the same class, reached twice, came to the same thing. What was met is how far this
 * compiler got on the way there, and two walks that got different distances both got theirs — a
 * figure one of them ran into is a number somebody can raise whether or not the other reached it.
 *
 * <p>Left to whatever holds them, they were joined by whether the whole answer was equal. A set of
 * them then held one word twice, with half the figures apiece: a reader met the same class in two
 * lines and could act on neither. So the law is the value's and is applied where a list becomes the
 * value that travels, which is what these check — one carrier apiece, because a carrier that
 * forgets it is a carrier nothing downstream can read correctly.
 */
class OneWordIsOneAnswerAndWhatWasMetUnderItAddsUpTest {

    private static final Generator.UnresolvedCombination NOTHING_COMPOSED =
            new Generator.UnresolvedCombination(List.of("days=low"),
                    Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);

    private static final Generator.UnresolvedCombination ANOTHER_WORD =
            new Generator.UnresolvedCombination(List.of("days=high"),
                    Generator.UnresolvedCombination.Reason.ALL_CANDIDATES_REJECTED);

    private static final CameToNothing STOPPED_AT_ONE = new CameToNothing(NOTHING_COMPOSED,
            CompositionShortfall.of(List.of(CompositionBudget.NUMBERS_OF_A_SET_TRIED)));

    private static final CameToNothing STOPPED_AT_ANOTHER = new CameToNothing(NOTHING_COMPOSED,
            CompositionShortfall.of(List.of(CompositionBudget.STEPS_A_SEARCH_MAY_TAKE)));

    private static final CameToNothing STOPPED_AT_BOTH = new CameToNothing(NOTHING_COMPOSED,
            CompositionShortfall.of(List.of(CompositionBudget.NUMBERS_OF_A_SET_TRIED,
                    CompositionBudget.STEPS_A_SEARCH_MAY_TAKE)));

    /** The law itself: one answer per word, with what was met under it added up. */
    @Test
    void oneWordComesBackOnceWithEverythingMetUnderIt() {
        assertEquals(List.of(STOPPED_AT_BOTH),
                CameToNothing.joined(List.of(STOPPED_AT_ONE, STOPPED_AT_ANOTHER)));
    }

    /** And two words stay two answers, in the order they were first met. */
    @Test
    void twoWordsStayTwoAnswersInTheOrderTheyWereMet() {
        CameToNothing other = CameToNothing.metNothing(ANOTHER_WORD);

        assertEquals(List.of(other, STOPPED_AT_ONE),
                CameToNothing.joined(List.of(other, STOPPED_AT_ONE)),
                "the order the words were first met, which is the order a search met them in");
    }

    /** What an arm came to at each of its places is one answer per word. */
    @Test
    void anArmsPlacesComeToOneAnswerPerWord() {
        assertEquals(new ArmDisposition.Unresolved(List.of(STOPPED_AT_BOTH)),
                new ArmDisposition.Unresolved(List.of(STOPPED_AT_ONE, STOPPED_AT_ANOTHER)));
    }

    /** And so does what the runs of one plan came to at an arm. */
    @Test
    void theRunsOfOnePlanComeToOneAnswerPerWordAtAnArm() {
        assertEquals(
                ArmDisposition.acrossRuns(
                        List.of(new ArmDisposition.Unresolved(List.of(STOPPED_AT_BOTH)))),
                ArmDisposition.acrossRuns(List.of(
                        new ArmDisposition.Unresolved(List.of(STOPPED_AT_ONE)),
                        new ArmDisposition.Unresolved(List.of(STOPPED_AT_ANOTHER)))),
                "both figures under the one word, and not the word twice with one apiece");
    }

    /** And what the runs came to at a class, which holds them to one word besides. */
    @Test
    void theRunsOfOnePlanComeToOneAnswerPerWordAtAClass() {
        assertEquals(new ClassDisposition.AcrossRuns.Unresolved(STOPPED_AT_BOTH),
                ClassDisposition.acrossRuns(List.of(
                        new ClassDisposition.Unresolved(STOPPED_AT_ONE),
                        new ClassDisposition.Unresolved(STOPPED_AT_ANOTHER))));
    }

    /** And every attempt a finding was answered by. */
    @Test
    void theAttemptsAFindingCameToAreOneAnswerPerWord() {
        assertEquals(new GenerationOutcome.CannotGenerate(List.of(STOPPED_AT_BOTH)),
                new GenerationOutcome.CannotGenerate(
                        List.of(STOPPED_AT_ONE, STOPPED_AT_ANOTHER)));
    }
}
