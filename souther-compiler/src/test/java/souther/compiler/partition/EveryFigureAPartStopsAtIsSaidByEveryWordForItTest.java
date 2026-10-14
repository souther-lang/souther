package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.BlockReason;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.WhyNotTaken;
import souther.compiler.meaning.WhyUnread;
import souther.compiler.observe.Figure;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * Every reason a part stopped at a figure is said, with that figure, by every vocabulary a report
 * says a figure in.
 *
 * <p>Which figure a reason stopped at is the reason's to say ({@link WhyUnread#figure}), and the
 * words a gap or a rule that drew no line is said in each hold the reason they say rather than a
 * figure of their own. What is left to drift is a reason added with no word for it, which would be
 * said as a part no wider run reads; so each such reason is looked up here in each vocabulary.
 *
 * <p>Over the reasons that hold nothing, which are the ones a figure stops: a figure is fixed where
 * it is declared, so a reason stopping at one carries nothing beside it.
 */
class EveryFigureAPartStopsAtIsSaidByEveryWordForItTest {

    /** Each reason that holds nothing and stopped at a figure. */
    private static List<WhyUnread> stoppedAtAFigure() throws Exception {
        List<WhyUnread> out = new ArrayList<>();
        for (Class<?> kind : WhyUnread.class.getPermittedSubclasses()) {
            if (kind.isRecord() && kind.getRecordComponents().length == 0) {
                WhyUnread why = (WhyUnread) kind.getDeclaredConstructor().newInstance();
                if (why.figure().isPresent()) {
                    out.add(why);
                }
            }
        }
        return out;
    }

    @Test
    void thereAreReasonsThatStopAtAFigure() throws Exception {
        assertFalse(stoppedAtAFigure().isEmpty(), "a walk that finds none checks nothing");
    }

    @Test
    void aGapOnTheWaySaysEachWithItsFigure() throws Exception {
        for (WhyUnread why : stoppedAtAFigure()) {
            ReadingGap.ReachNotRead gap = ReadingGap.ReachNotRead.of(why);
            assertEquals(why, gap.why().says(), why::toString);
            assertEquals(List.of(why.figure().orElseThrow()), gap.figures(), why::toString);
        }
    }

    @Test
    void aRuleThatDrewNoLineSaysEachWithItsFigure() throws Exception {
        for (WhyUnread why : stoppedAtAFigure()) {
            BlockReason.WhatItStatesIsNoLine said =
                    Cutting.whatItStates(new Proposition.Always(true), List.of(why));
            assertEquals(why, said.why().says(), why::toString);
            assertEquals(List.of(why.figure().orElseThrow()), said.figures(), why::toString);
        }
    }

    /** And a composer of an answer names the budget, where the figure is one. */
    @Test
    void aComposerNamesTheBudgetOfEach() throws Exception {
        for (WhyUnread why : stoppedAtAFigure()) {
            AnAnswerComposed.Ways ways = AnAnswerComposed.written(List.of(
                    new DemandReading.Read.Unread(new WhyNotTaken.MeaningUnread(why))));
            Figure figure = why.figure().orElseThrow();
            assertEquals(figure instanceof Figure.Budget(CompositionBudget budget)
                            ? new AnAnswerComposed.Ways.Stopped(Set.of(budget))
                            : new AnAnswerComposed.Ways.Unwritable(),
                    ways, why::toString);
        }
    }
}
