package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.Allowances;
import souther.compiler.partition.CompositionBudget;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A budget is held to the figure its compilation says, while the compilation answers and nowhere
 * else; the figure is said before anything is asked; and a figure is said only for a budget every
 * reader asks where it uses it.
 */
class AFigureIsHeldToWhatItsCompilationSaysTest {

    private static final CompositionBudget SETTABLE =
            CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO;

    /** A question whose answer is the figure in force where it is worked out. */
    private record TheFigure() implements Key<Integer> {

        @Override
        public Answer<Integer> compute(Db db) {
            return Answer.of(SETTABLE.maximum());
        }
    }

    @Test
    void aStoreAnswersUnderTheFiguresItWasSetUpWith() {
        Allowances fewer = Allowances.DECLARED.with(SETTABLE, 3);
        Db db = new Db().allowing(fewer);

        assertEquals(3, db.ask(new TheFigure()).value(), "held to what the store says");
        assertEquals(SETTABLE.declared(), SETTABLE.maximum(), "and outside it, as declared");
        assertEquals(SETTABLE.declared(), new Db().ask(new TheFigure()).value(),
                "a store that says nothing holds the figure declared");
    }

    @Test
    void theFiguresAreSaidBeforeAnythingIsAsked() {
        Db db = new Db();
        db.ask(new TheFigure());

        assertSame(db, db.allowing(Allowances.DECLARED), "the figures it answered under again");
        assertThrows(IllegalStateException.class,
                () -> db.allowing(Allowances.DECLARED.with(SETTABLE, 3)),
                "another figure would leave every answer it kept worked out under the first");
    }

    @Test
    void aFigureIsSaidOnlyForABudgetReadWhereItIsUsed() {
        CompositionBudget copied = CompositionBudget.PAIRINGS_BUILT_AT_ONCE;
        assertThrows(IllegalArgumentException.class, () -> Allowances.DECLARED.with(copied, 3),
                "a figure a class copies when it is loaded would be said and not held");
        assertEquals(Allowances.DECLARED, Allowances.DECLARED.with(SETTABLE, 3)
                        .with(SETTABLE, SETTABLE.declared()),
                "the figure declared, said again, is nothing said");
    }
}
