package souther.test;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * That {@link GitIndex} refuses when git does not answer, rather than answering for it.
 *
 * <p>Everything built on it holds an invariant over the files the repository owns. Without git that
 * set is unobserved, which is not the same as its being empty — an empty list would satisfy every
 * one of those invariants by having nothing to hold them over.
 *
 * <p>What has no control here is the two-minute bound on a git that never finishes. Writing one
 * would mean a process that hangs on purpose, and the portable ways to get one are worse than the
 * thing they would be testing. What stands in its place is the order the streams are read in: both
 * go to files, so the wait for the process is the first thing that blocks, and there is no read of
 * a pipe for it to be unreachable behind.
 */
class WhenGitCannotAnswerNothingIsReturnedInsteadTest {

    private static final RepositoryLayout REPOSITORY = RepositoryLayout.ofWorkingDirectory();

    @Test
    void gitRefusingIsRefusedAndNotReadAsAnEmptyRepository() {
        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> GitIndex.of(REPOSITORY, "ls-files", "--no-such-option"));

        assertTrue(refused.getMessage().contains("exited"),
                "it says git refused: " + refused.getMessage());
        assertTrue(refused.getMessage().contains("no-such-option"),
                "and says what git said about it: " + refused.getMessage());
    }

    /** And the reading it is the refusal of works, so the refusal is about the option. */
    @Test
    void andTheSameReadingWithoutItAnswers() {
        assertEquals(GitIndex.of(REPOSITORY).trackedFiles(),
                GitIndex.of(REPOSITORY, "ls-files", "-z", "--cached").trackedFiles());
        assertTrue(GitIndex.of(REPOSITORY).trackedFiles().size() > 1000,
                "this repository holds files");
    }

    /** What the ordinary reading asks for, so the control above is the same question. */
    @Test
    void andThatIsTheReadingTheOrdinaryOneMakes() {
        assertEquals(List.of("ls-files", "-z", "--cached"), GitIndex.LS_FILES);
    }
}
