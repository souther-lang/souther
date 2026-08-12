package souther.compiler.ast;

import souther.compiler.diag.SourcePos;
import souther.compiler.types.ReachName;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A name says what it denotes and how this module reaches it, or it says neither.
 *
 * <p>Both answers come from resolution and they are two halves of one question. A reader that has
 * one and not the other is holding a reference that resolves to a declaration and reaches nothing,
 * or the other way round — and the reader after it takes the spelling instead, which is what a table
 * keyed by names answers with silence.
 *
 * <p>So the halves are refused where they are put together rather than caught where they are read.
 * A rewrite that carries a name across and drops one of them is a mistake in this compiler, and the
 * place to say so is the one that could have carried both.
 */
class ANameAnsweredHalfwayIsRefusedTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    private static final ValueName.Helper DECLARED = new ValueName.Helper("demo", "spin");

    /** A name the parser read: nothing has been answered about it yet, and that is a state. */
    @Test
    void aNameNothingHasAnsweredYetIsFine() {
        Ast.Var written = new Ast.Var("spin", POS);

        assertEquals("spin", written.name());
        assertEquals("spin", written.reaches(),
                "nothing resolved it, so what it reaches is what it is written as");
    }

    /** What it denotes without how it is reached is not a state a rewrite may leave behind. */
    @Test
    void aNameThatDenotesSomethingAndReachesNothingCannotBeBuilt() {
        IllegalArgumentException refused = assertThrows(IllegalArgumentException.class,
                () -> new Ast.Var(WrittenName.of("spin", POS), DECLARED, null));

        assertEquals(true, refused.getMessage().contains("spin"), refused.getMessage());
    }

    /** And a reader asking what a name is declared as, of one nothing answered, is told so rather
     * than handed the spelling — the answer it wanted is the one that is missing. */
    @Test
    void theDeclaredNameOfSomethingNothingAnsweredIsRefused() {
        Ast.Var written = new Ast.Var("spin", POS);

        assertThrows(IllegalStateException.class, written::bare);
    }

    /** Answered, it says both. */
    @Test
    void aResolvedNameSaysWhatItDenotesAndHowItIsReached() {
        Ast.Var resolved = new Ast.Var(WrittenName.of("spin", POS), DECLARED,
                new ReachName.OfModule("demo", "spin"));

        assertEquals("spin", resolved.bare());
        assertEquals("demo.spin", resolved.reaches());
    }
}
