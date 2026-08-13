package souther.compiler.ast;

import souther.compiler.diag.SourcePos;
import souther.compiler.types.TypeName;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The three states a type name is in, and the one that used to stand for two of them.
 *
 * <p>Resolution answers a name or finds nothing declares it, and before it runs neither has
 * happened. Those are three things. They were two — a name carried the declaration it denotes, and
 * a name nothing declared carried a stand-in identity under a module called {@code unresolved}, so
 * "has this been resolved" and "does this name something" were one question read off one value.
 *
 * <p>A reader downstream of the pass got a name that answered the first and lied about the second.
 * What it did with the lie was its own business: {@code TypeOps.fieldTypes} looked the stand-in up,
 * found no declaration and reported that the spread was not a product data; {@code MatchElaborator}
 * compared it against {@code Some} and {@code None} and reported that the arm was not a case of an
 * optional. Both are the unknown name reported a second time, in words that send the author
 * somewhere else.
 */
class ANameNothingDeclaresIsNotAResolvedNameTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    private static final TypeName DECLARED = new TypeName("demo", "Invoice");

    /** Before the pass runs, a name is what it is written as and nothing else. */
    @Test
    void aNameNothingHasReadYetRefusesTheQuestion() {
        Ast.Name written = Ast.Name.written("Invoice", POS);

        assertEquals("Invoice", written.written());
        IllegalStateException e = assertThrows(IllegalStateException.class, written::denotes);
        assertTrue(e.getMessage().contains("before it was resolved"), e.getMessage());
    }

    /**
     * Read and found nothing, it refuses the same question — and says the other thing, because what
     * a reader does next differs. One of these is a fault in the compiler; the other is a mistake in
     * the source that was reported where it is written.
     */
    @Test
    void aNameNothingDeclaresRefusesItToo() {
        Ast.Name unanswered = Ast.Name.written("Invoice", POS).unanswered();

        assertEquals("Invoice", unanswered.written());
        IllegalStateException e = assertThrows(IllegalStateException.class, unanswered::denotes);
        assertTrue(e.getMessage().contains("denotes nothing"), e.getMessage());
    }

    /**
     * And a resolved name holds a declaration that is there. The stand-in cannot be put in one, so
     * there is no value that says it has been resolved and names nothing — which is the state every
     * reader below the pass was left to notice for itself.
     */
    @Test
    void aResolvedNameCannotCarryAStandIn() {
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> Ast.Name.written("Invoice", POS).denoting(TypeName.unresolved("Invoice")));

        assertTrue(e.getMessage().contains("Unanswered"), e.getMessage());
    }

    /** Answered, it says which declaration. */
    @Test
    void aResolvedNameSaysWhatItDenotes() {
        assertEquals(DECLARED, Ast.Name.written("Invoice", POS).denoting(DECLARED).denotes());
    }
}
