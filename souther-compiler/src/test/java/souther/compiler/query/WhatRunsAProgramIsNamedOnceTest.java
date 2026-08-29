package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.execute.ConstantConstruction;
import souther.compiler.execute.ConstantOutcome;
import souther.compiler.execute.ExampleExecution;
import souther.compiler.execute.ProgramExecution;
import souther.compiler.execute.BoundaryValues;
import souther.compiler.execute.RowTrials;
import souther.compiler.observe.ArmObservation;
import souther.compiler.observe.RowRun;
import souther.compiler.observe.StatementReading;
import souther.compiler.observe.TableBuild;
import souther.compiler.source.SourceId;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * What runs a compilation's programs is named where the compilation is set up, and not again.
 *
 * <p>It sits beside the memos rather than in them, which is what an answer being a value requires
 * — and that is exactly why a second one may not be named. A key that ran a program did not record
 * reading the runner, so an answer worked out under the first is not invalidated by the second, and
 * the store would go on handing out the first one's answers under the second one's name. Nothing
 * would report that; the numbers would simply be someone else's.
 */
class WhatRunsAProgramIsNamedOnceTest {

    @Test
    void aStoreTakesWhatRunsItsProgramsOnce() {
        Db db = new Db().running(new NothingRuns());

        assertThrows(IllegalStateException.class, () -> db.running(new NothingRuns()),
                "a second runner would leave the first one's answers standing under its name");
    }

    @Test
    void andTheOneItTookIsTheOneItAnswersWith() {
        ProgramExecution named = new NothingRuns();
        Db db = new Db().running(named);

        assertSame(named, db.execution());
    }

    @Test
    void aStoreThatWasNeverGivenOneSaysSoRatherThanFailingWhereItIsUsed() {
        Db db = new Db();

        assertEquals("nothing was named to run this compilation's programs",
                assertThrows(IllegalStateException.class, db::execution).getMessage());
    }

    /** Enough of one to be named. Nothing asks it anything here. */
    private static final class NothingRuns implements ProgramExecution {

        @Override
        public ConstantOutcome check(ConstantConstruction written) {
            return new ConstantOutcome.NotEvaluatedHere();
        }

        @Override
        public RowRun run(ExampleExecution asked, SourceId source, ArmObservation arms) {
            return new RowRun.NotRunHere();
        }

        @Override
        public TableBuild fakeTables(ExampleExecution asked, SourceId source) {
            return new TableBuild.NotBuiltHere();
        }

        @Override
        public StatementReading statements(ExampleExecution asked) {
            return new StatementReading.NotReadHere();
        }

        @Override
        public BoundaryValues values(ExampleExecution asked) {
            return null;
        }

        @Override
        public RowTrials trials(ExampleExecution asked, ArmObservation arms) {
            return null;
        }
    }
}
