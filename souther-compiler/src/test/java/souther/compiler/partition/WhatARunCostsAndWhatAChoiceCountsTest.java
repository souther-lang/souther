package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.coverage.AlignedObservation;
import souther.compiler.coverage.ArmReplacements;
import souther.compiler.coverage.Runs;
import souther.compiler.coverage.SiteNumbering;
import souther.compiler.observe.AnswerChange;
import souther.compiler.observe.AnswerObservation;
import souther.compiler.observe.ObservedValue;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.types.SourceConstructOrigin;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.TreeMap;
import java.util.function.LongUnaryOperator;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * What a search may spend is the runs nobody made before, and what the choice among rows counts is
 * the rows that meet what they were composed for.
 *
 * <p>Two figures, each asked of the one thing it bounds. A run made once is free to every search
 * after it — the row's own and the row's under a rewrite alike — so a search with a figure of its
 * own is stopped only by runs it had to make. And a row composed on the way to one that meets the
 * requirement is no candidate, so it does not use up the rows the choice may rank.
 */
class WhatARunCostsAndWhatAChoiceCountsTest {

    /** A run of the row and a run of it under a rewrite, each asked for twice. */
    @Test
    void aRunMadeBeforeIsNotSpentAgainForTheRowOrForItsRewrite() {
        Counting trial = new Counting(numbering(), _ -> 0);
        Generator.RunOnce once = Generator.runningOnce(trial);
        RowToRun row = row(7);
        int[] spent = {0};
        Generator.Spend spend = () -> {
            spent[0]++;
            return true;
        };

        once.run(row, spend);
        once.run(row, spend);
        once.runReplacing(row, Map.of(3, 1), spend);
        once.runReplacing(row, Map.of(3, 1), spend);

        assertEquals(2, spent[0], "one run of the row and one under the rewrite were made");
        assertEquals(List.of("run 7", "rewritten 7"), trial.made);
    }

    /** A search with nothing left is still answered from the runs made before it. */
    @Test
    void aRunMadeBeforeIsAnsweredWithNothingLeftToSpend() {
        Generator.RunOnce once = Generator.runningOnce(new Counting(numbering(), _ -> 0));
        RowToRun row = row(7);
        once.run(row);
        once.runReplacing(row, Map.of(3, 1));

        assertNotNull(once.run(row, () -> false), "the row was run already");
        assertNotNull(once.runReplacing(row, Map.of(3, 1), () -> false),
                "and so was it under the rewrite");
        assertNull(once.run(row(8), () -> false), "a row nobody ran needs a run");
    }

    /**
     * Rows that do not meet the requirement, more of them than the choice may rank, between the
     * first that does and one that tells the rewrite apart, use up nothing the choice counts.
     */
    @Test
    void rowsThatDoNotMeetTheRequirementAreNotCountedAgainstTheChoice() {
        // A row holding 1 answers differently under the rewrite; one holding 0 does not.
        Generator.TellingArmsApart choosing = new Generator.TellingArmsApart(
                new Counting(numbering(), value -> value), List.of());
        Generator.RowTaking taking = choosing.over(inputs -> text(inputs).startsWith("-")
                ? Generator.Acceptance.PASSED : Generator.Acceptance.TAKEN);

        taking.take(List.of(FixtureTemplate.integer(0)));
        for (int i = 1; i <= Generator.MOST_ROWS_OFFERED_FOR_THE_ARMS; i++) {
            assertEquals(Generator.Acceptance.PASSED,
                    taking.take(List.of(FixtureTemplate.integer(-i))));
        }

        assertEquals(Generator.Acceptance.TAKEN, taking.take(List.of(FixtureTemplate.integer(1))));
        assertEquals("1", text(choosing.taken()));
    }

    /** A row composed again is the row ranked already, and is not ranked a second time. */
    @Test
    void aRowComposedAgainIsNotCountedAgainstTheChoice() {
        Generator.TellingArmsApart choosing = new Generator.TellingArmsApart(
                new Counting(numbering(), value -> value), List.of());
        Generator.RowTaking taking = choosing.over(_ -> Generator.Acceptance.TAKEN);

        for (int i = 0; i <= Generator.MOST_ROWS_OFFERED_FOR_THE_ARMS; i++) {
            assertEquals(Generator.Acceptance.PASSED,
                    taking.take(List.of(FixtureTemplate.integer(0))));
        }

        assertEquals(Generator.Acceptance.TAKEN, taking.take(List.of(FixtureTemplate.integer(1))));
        assertEquals("1", text(choosing.taken()));
    }

    /** Where every row it may rank tells nothing apart, the first of them is taken. */
    @Test
    void theFirstRowIsTakenWhereNoneRankedTellsMore() {
        Generator.TellingArmsApart choosing = new Generator.TellingArmsApart(
                new Counting(numbering(), _ -> 0), List.of());
        Generator.RowTaking taking = choosing.over(_ -> Generator.Acceptance.TAKEN);

        Generator.Acceptance last = null;
        for (int i = 0; i < Generator.MOST_ROWS_OFFERED_FOR_THE_ARMS; i++) {
            last = taking.take(List.of(FixtureTemplate.integer(10 + i)));
        }

        assertEquals(Generator.Acceptance.STOPPED, last, "the figure is reached at the last row");
        assertEquals("10", text(choosing.taken()));
    }

    private static String text(List<FixtureTemplate> inputs) {
        return inputs.getFirst().text();
    }

    private static RowToRun row(long value) {
        return new RowToRun(List.of(FixtureTemplate.integer(value)), List.of());
    }

    private static SiteNumbering numbering() {
        Compilation compilation = Compilation.ofSource("""
                module example.one
                behavior one : (n: Int) -> Int
                let one (n) = if n > 0 then n else 0
                """, "Main");
        compilation.answerEverything();
        Bodies.Elaborated checked = compilation.db()
                .ask(new Bodies.Checked(compilation.modules().getFirst())).value();
        assertNotNull(checked);
        return checked.plan().numbering();
    }

    /**
     * Rows that all go one way and answer 0, one rewrite of the arm on it, and the rewrite
     * answering what {@code answering} makes of the row's value — with every run it is asked for
     * written down.
     */
    private static final class Counting implements Generator.Trial {

        private final SiteNumbering numbering;
        private final LongUnaryOperator answering;
        private final List<String> made = new ArrayList<>();

        private Counting(SiteNumbering numbering, LongUnaryOperator answering) {
            this.numbering = numbering;
            this.answering = answering;
        }

        @Override
        public Generator.ObservedRun run(RowToRun row) {
            made.add("run " + row.inputs().getFirst().text());
            return new Generator.ObservedRun(new Generator.Watched.Ran(Runs.nowhere(numbering)),
                    new AnswerObservation.Answered(new ObservedValue.Integer(0)));
        }

        @Override
        public Optional<AnswerObservation> runReplacing(RowToRun row,
                                                        Map<Integer, Integer> replacing) {
            made.add("rewritten " + row.inputs().getFirst().text());
            return Optional.of(new AnswerObservation.Answered(new ObservedValue.Integer(
                    answering.applyAsLong(Long.parseLong(row.inputs().getFirst().text())))));
        }

        @Override
        public AnswerChange change(AnswerObservation was, AnswerObservation now) {
            return was.equals(now) ? AnswerChange.SAME : AnswerChange.CHANGED;
        }

        @Override
        public List<ArmReplacements.Rewrite> rewritesThrough(AlignedObservation ran) {
            return List.of(new ArmReplacements.Rewrite(SourceConstructOrigin.unwritten(), 0, 1,
                    new TreeMap<>(Map.of(3, 1))));
        }
    }
}
