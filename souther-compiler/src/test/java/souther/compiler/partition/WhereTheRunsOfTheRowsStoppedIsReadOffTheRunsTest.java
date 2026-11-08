package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.execute.RunStop;
import souther.compiler.observe.AnswerObservation;

import java.util.List;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where the runs of the rows a walk composed stopped is read off the runs, which every row of a
 * search is run through ({@link Generator.RunOnce}), and not off whichever preference was looking:
 * a judge that runs a row to say whether it is the one looked for and refuses it leaves what the
 * run stopped at as much as a ranking that runs the row itself.
 */
class WhereTheRunsOfTheRowsStoppedIsReadOffTheRunsTest {

    private static final WhereARunStopped STOP = new WhereARunStopped(new RunStop.AtAConstruction(
            "m", "T", Optional.empty(), 0, "m", 8, 23), Optional.empty());

    /** A trial whose every run stops at {@link #STOP}, run once per row. */
    private static Generator.Trial stopping() {
        return Generator.once(_ -> new Generator.ObservedRun(new Generator.Watched.NoAccount(),
                new AnswerObservation.NotAnswered(), Optional.of(STOP)));
    }

    /** A trial whose every run goes past what a run may spend. */
    private static Generator.Trial runningOut() {
        return Generator.once(_ -> new Generator.ObservedRun(new Generator.Watched.NoAccount(),
                new AnswerObservation.RanOut(Optional.empty()), Optional.empty()));
    }

    /** A judge that runs the row through {@code trial} and refuses it whatever it came to. */
    private static Generator.RowJudge runningAndRefusing(Generator.Trial trial) {
        return row -> {
            trial.run(row);
            return false;
        };
    }

    private static void handOne(Generator.RowPreference preference) {
        preference.over(_ -> Generator.Acceptance.TAKEN).take(List.of(FixtureTemplate.integer(0)));
    }

    @Test
    void aJudgeThatRefusedARowItRanSaysWhereTheRunStopped() {
        Generator.Trial trial = stopping();
        Generator.ReachingWhatIsJudged judged = new Generator.ReachingWhatIsJudged(
                runningAndRefusing(trial), List.of(), trial);
        Generator.TellingArmsApart ranked = new Generator.TellingArmsApart(trial, List.of());

        handOne(judged);
        handOne(ranked);

        assertEquals(Set.of(STOP), judged.stoppedAt());
        assertEquals(Set.of(STOP), ranked.stoppedAt());
    }

    @Test
    void aJudgeThatRefusedARowItRanSaysTheRunRanOut() {
        Generator.Trial trial = runningOut();
        Generator.ReachingWhatIsJudged judged = new Generator.ReachingWhatIsJudged(
                runningAndRefusing(trial), List.of(), trial);
        Generator.TellingArmsApart ranked = new Generator.TellingArmsApart(trial, List.of());

        handOne(judged);
        handOne(ranked);

        assertTrue(judged.aRunRanOut());
        assertTrue(ranked.aRunRanOut());
    }

    /** A row the requirement turned away was never put to the judge, and nothing ran it. */
    @Test
    void aRowNeverPutToTheJudgeStoppedNowhere() {
        Generator.Trial trial = stopping();
        trial.run(new RowToRun(List.of(FixtureTemplate.integer(0)), List.of()));
        Generator.ReachingWhatIsJudged judged = new Generator.ReachingWhatIsJudged(
                runningAndRefusing(trial), List.of(), trial);

        judged.over(_ -> Generator.Acceptance.PASSED).take(List.of(FixtureTemplate.integer(0)));

        assertEquals(Set.of(), judged.stoppedAt());
    }
}
