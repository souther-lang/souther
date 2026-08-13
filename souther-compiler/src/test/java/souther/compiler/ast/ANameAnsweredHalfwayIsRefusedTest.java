package souther.compiler.ast;

import souther.compiler.diag.SourcePos;
import souther.compiler.types.ConstructionOrigin;
import souther.compiler.types.ReachName;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.List;

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

    /**
     * A name the parser read: nothing has been answered about it yet, and that is a state. It says
     * what it is written as, and refuses both questions that are about a declaration rather than
     * about the characters — the answer either wants is the one that is missing, and handing back
     * the spelling is what a table keyed by declarations misses on.
     */
    @Test
    void aNameNothingHasAnsweredYetSaysOnlyWhatItIsWrittenAs() {
        Ast.Var written = new Ast.Var("spin", POS);

        assertEquals("spin", written.name());
        assertThrows(IllegalStateException.class, written::bare);
        assertThrows(IllegalStateException.class, written::reaches);
    }

    /**
     * Half an answer is not a state a rewrite may leave behind, whichever half it is. One way round
     * leaves a reference that resolves to a declaration and reaches nothing; the other leaves a key
     * with nothing saying what it means, and there is nowhere for it to have come from —
     * {@link ReachName#of} takes the denotation to work one out.
     */
    @Test
    void aNameAnsweredOnOneCountOnlyCannotBeBuilt() {
        IllegalArgumentException noReach = assertThrows(IllegalArgumentException.class,
                () -> new Ast.Var(WrittenName.of("spin", POS), DECLARED, null));
        IllegalArgumentException noDenotation = assertThrows(IllegalArgumentException.class,
                () -> new Ast.Var(WrittenName.of("spin", POS), null,
                        new ReachName.OfModule("demo", "spin")));

        assertEquals(true, noReach.getMessage().contains("spin"), noReach.getMessage());
        assertEquals(true, noDenotation.getMessage().contains("spin"), noDenotation.getMessage());
    }

    /**
     * And a pass applying a name says what it means. The application a pass writes takes both
     * answers and takes them as answers: the constructor that took a spelling alone is gone, and
     * this is the one that replaced it, so a caller with nothing to say cannot say it here either.
     *
     * <p>Refused at the application rather than left to {@link Ast.Var}, which admits the pair
     * being absent — that is the parser's state, and the parser builds its own callee. A pass has
     * resolution behind it or is writing a name for someone downstream to resolve, which is what
     * ADR-0067 rules out.
     */
    @Test
    void anApplicationAPassWritesCannotLeaveItsNameUnanswered() {
        assertThrows(NullPointerException.class,
                () -> new Ast.Apply("spin", null, new ReachName.OfModule("demo", "spin"),
                        List.of(), ConstructionOrigin.own(), POS, null));
        assertThrows(NullPointerException.class,
                () -> new Ast.Apply("spin", DECLARED, null,
                        List.of(), ConstructionOrigin.own(), POS, null));
        assertThrows(NullPointerException.class,
                () -> new Ast.Apply("spin", null, null,
                        List.of(), ConstructionOrigin.own(), POS, null));
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
