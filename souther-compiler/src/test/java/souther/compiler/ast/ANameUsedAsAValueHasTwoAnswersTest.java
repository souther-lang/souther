package souther.compiler.ast;

import souther.compiler.diag.Region;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.ReachName;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * As {@link Hir.Name} for a type, so for a name used as a value: answered, or read and found to name
 * nothing.
 *
 * <p>The second was a denotation like any other — {@code ValueName.Unresolved}, carrying the
 * spelling — so a reader below the pass held a name that said it had been resolved and named
 * nothing. Every walk over a body had to know that: the switch over what a name denotes carried an
 * arm for it that answered null, 0 or false, and a walk that forgot the arm would not have compiled
 * but a walk that wrote it wrongly would.
 *
 * <p>It is a state of the reference now, not a kind of denotation, so a walk asks which of the two
 * it has and the one that names nothing has neither answer to give.
 *
 * <p>There were three. The third — read by nobody — was a state of the same type, which made "has
 * this been looked at" and "did it name something" two readings of one value. It is
 * {@link Ast.Var} now: a different representation, on the other side of {@code Resolve}, and not
 * something a reader here can be handed.
 */
class ANameUsedAsAValueHasTwoAnswersTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    private static final ValueName DECLARED = new ValueName.Helper("demo", "spin");

    private static final ReachName REACHED = new ReachName.OfModule("demo", "spin");

    private static Hir.Var denoting(WrittenName name) {
        return new Hir.Var.Denoting(name, DECLARED, REACHED, name.region());
    }

    private static Hir.Var unanswered(WrittenName name) {
        return new Hir.Var.Unanswered(name, name.region());
    }

    /** Read and found nothing, a name refuses both answers — and says which of the two questions it
     * is refusing, because what a reader does about each differs. */
    @Test
    void aNameNothingAnswersToRefusesBothAnswers() {
        Hir.Var nothing = unanswered(WrittenName.of("spin", POS));

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
        Hir.Var answered = denoting(WrittenName.of("spin", POS));

        assertEquals("spin", answered.bare());
        assertEquals("demo.spin", answered.reaches());
        assertFalse(answered.unresolved());

        assertThrows(IllegalArgumentException.class,
                () -> new Hir.Var.Denoting(WrittenName.of("spin", POS), DECLARED, null, null));
        assertThrows(IllegalArgumentException.class,
                () -> new Hir.Var.Denoting(WrittenName.of("spin", POS), null, REACHED, null));
    }

    /**
     * Each answer keeps its own kind when the expression it is gets a new extent — a name the author
     * parenthesized is written over five characters and is an expression over nine.
     */
    @Test
    void anExtentDoesNotChangeWhichOfTheTwoItIs() {
        WrittenName name = WrittenName.synthetic("spin", POS);
        Region wider = new Region(POS, new SourcePos(1, 10));

        assertEquals(Hir.Var.Unanswered.class,
                Hir.withRegion(unanswered(name), wider).getClass());
        assertEquals(Hir.Var.Denoting.class,
                Hir.withRegion(denoting(name), wider).getClass());
    }

    /** And there is no third kind for an extent to keep. */
    @Test
    void aNameNothingHasReadIsNotOneOfThem() {
        assertEquals(Set.of(Hir.Var.Denoting.class, Hir.Var.Unanswered.class),
                Set.of(Hir.Var.class.getPermittedSubclasses()));
    }
}
