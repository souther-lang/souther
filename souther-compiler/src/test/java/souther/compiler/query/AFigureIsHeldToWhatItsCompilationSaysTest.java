package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.observe.Figure;
import souther.compiler.partition.Allowances;
import souther.compiler.partition.CompositionBudget;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
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

    /** A question whose answer is the figure reached, as a reader is told it. */
    private record TheFigureReached() implements Key<Figure> {

        @Override
        public Answer<Figure> compute(Db db) {
            return Answer.of(SETTABLE.figure());
        }
    }

    /**
     * A figure reached carries the number it stood at: told after the store answered, it says
     * the store's, and figures two stores reached at two numbers are two figures.
     */
    @Test
    void aFigureReachedIsTheNumberItStoodAt() {
        Figure reached = new Db().allowing(Allowances.DECLARED.with(SETTABLE, 3))
                .ask(new TheFigureReached()).value();
        assertEquals("3", reached.most(), "the store's figure, told outside it");
        Figure declared = new Db().ask(new TheFigureReached()).value();
        assertEquals(Integer.toString(SETTABLE.declared()), declared.most());
        assertNotEquals(declared, reached, "a budget reached at two numbers is two figures");
    }

    /**
     * A budget a compilation may set is made a figure only while one answers: made after, it
     * would say the figure declared whatever the compilation that reached it was held to. A store
     * holding every figure to the one declared puts them in force as well.
     */
    @Test
    void aFigureACompilationMaySetIsMadeOnlyWhileOneAnswers() {
        assertThrows(IllegalStateException.class, SETTABLE::figure,
                "no compilation answering, so no figure it stood at");
        assertEquals(new Figure.Budget(SETTABLE, SETTABLE.declared()),
                new Db().ask(new TheFigureReached()).value(),
                "a store holding the figures declared answers under them");
        CompositionBudget fixed = CompositionBudget.PAIRINGS_BUILT_AT_ONCE;
        assertEquals(new Figure.Budget(fixed, fixed.declared()), fixed.figure(),
                "a budget no compilation may set stands at the one declared anywhere");
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
