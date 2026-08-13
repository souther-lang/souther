package souther.compiler.ast;

import souther.compiler.diag.Region;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.ReachName;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * As {@link Ast.Name} for a type, so for a name used as a value: read by nobody, answered, or read
 * and found to name nothing.
 *
 * <p>The third was a denotation like any other — {@code ValueName.Unresolved}, carrying the spelling
 * — so a reader below the pass held a name that said it had been resolved and named nothing. Every
 * walk over a body had to know that: the switch over what a name denotes carried an arm for it that
 * answered null, 0 or false, and a walk that forgot the arm would not have compiled but a walk that
 * wrote it wrongly would.
 *
 * <p>It is a state of the reference now, not a kind of denotation, so a walk asks which of the three
 * it has and the one that names nothing has neither answer to give.
 */
class ANameUsedAsAValueHasThreeStatesTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    private static final ValueName DECLARED = new ValueName.Helper("demo", "spin");

    private static final ReachName REACHED = new ReachName.OfModule("demo", "spin");

    /** Before the pass runs, a name is what it is written as and nothing else. */
    @Test
    void aNameNothingHasReadYetRefusesBothAnswers() {
        Ast.Var written = Ast.Var.written("spin", POS);

        assertEquals("spin", written.name());
        assertFalse(written.unresolved(), "nothing has looked at it, so nothing found it wanting");
        assertTrue(assertThrows(IllegalStateException.class, written::bare)
                .getMessage().contains("before it was resolved"));
        assertThrows(IllegalStateException.class, written::reaches);
    }

    /**
     * Read and found nothing, it refuses both too — and says so as the other thing, because what a
     * reader does about it differs. A {@link Ast.Var.Written} one is a fault in this compiler; this
     * one is a mistake in the source, reported where it is written, and the definition holding it is
     * abandoned rather than diagnosed a second time.
     */
    @Test
    void aNameNothingAnswersToRefusesThemAsTheOtherThing() {
        Ast.Var nothing = Ast.Var.written("spin", POS).unanswered();

        assertEquals("spin", nothing.name());
        assertTrue(nothing.unresolved());
        assertTrue(assertThrows(IllegalStateException.class, nothing::bare)
                .getMessage().contains("denotes nothing"));
        assertThrows(IllegalStateException.class, nothing::reaches);
    }

    /**
     * And an answered one is answered on both counts. Half of it is not a state a rewrite may leave
     * behind: one way round leaves a reference that resolves to a declaration and reaches nothing,
     * the other a key with nothing saying what it means.
     */
    @Test
    void anAnsweredNameIsAnsweredOnBothCounts() {
        Ast.Var answered = Ast.Var.denoting(WrittenName.of("spin", POS), DECLARED, REACHED);

        assertEquals("spin", answered.bare());
        assertEquals("demo.spin", answered.reaches());
        assertFalse(answered.unresolved());

        assertThrows(IllegalArgumentException.class,
                () -> Ast.Var.denoting(WrittenName.of("spin", POS), DECLARED, null));
        assertThrows(IllegalArgumentException.class,
                () -> Ast.Var.denoting(WrittenName.of("spin", POS), null, REACHED));
    }

    /**
     * Every state keeps its own kind when the expression it is gets a new extent — a name the
     * author parenthesized is written over five characters and is an expression over nine.
     */
    @Test
    void anExtentDoesNotChangeWhichOfTheThreeItIs() {
        WrittenName name = WrittenName.synthetic("spin", POS);
        Region wider = new Region(POS, new SourcePos(1, 10));

        assertEquals(Ast.Var.Written.class,
                Ast.withRegion(Ast.Var.written(name), wider).getClass());
        assertEquals(Ast.Var.Unanswered.class,
                Ast.withRegion(Ast.Var.written(name).unanswered(), wider).getClass());
        assertEquals(Ast.Var.Denoting.class,
                Ast.withRegion(Ast.Var.denoting(name, DECLARED, REACHED), wider).getClass());
    }
}
