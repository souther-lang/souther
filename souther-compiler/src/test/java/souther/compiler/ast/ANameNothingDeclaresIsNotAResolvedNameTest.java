package souther.compiler.ast;

import souther.compiler.diag.SourcePos;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.TypeSymbol;

import org.junit.jupiter.api.Test;

import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The states a type name is in, and the one that used to stand for two of them.
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
 *
 * <p>The three are not three states of one type now. Two of them are answers, and they are
 * {@link Hir.Name}'s; the third is a name nothing has read, which is {@link Ast.Name} and carries no
 * slot an answer could go in. So a reader below the pass cannot be handed the third, and the
 * question that used to be read off one value is asked of the representation instead.
 */
class ANameNothingDeclaresIsNotAResolvedNameTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    private static final TypeSymbol DECLARED = TypeSymbols.declared(new TypeKey("demo", "Invoice"));

    /** Before the pass runs, a name is what it is written as and nothing else. */
    @Test
    void aNameNothingHasReadYetSaysOnlyWhatItIsWrittenAs() {
        Ast.Name written = Ast.Name.written("Invoice", POS);

        assertEquals("Invoice", written.written());
        assertEquals(Ast.Name.class, written.getClass(),
                "one form: what a name means is not something this representation can hold");
    }

    /**
     * Read and found nothing, it refuses the question — and says which of the two it is refusing,
     * because what a reader does next differs. This is a mistake in the source, reported where it is
     * written, and the declaration holding it has no meaning to work out.
     */
    @Test
    void aNameNothingDeclaresRefusesTheQuestion() {
        Hir.Name unanswered = new Hir.Name.Unanswered(WrittenName.of("Invoice", POS));

        assertEquals("Invoice", unanswered.written());
        IllegalStateException e = assertThrows(IllegalStateException.class, unanswered::denotes);
        assertTrue(e.getMessage().contains("denotes nothing"), e.getMessage());
    }

    /** Answered, it says which declaration. */
    @Test
    void aResolvedNameSaysWhatItDenotes() {
        assertEquals(DECLARED,
                new Hir.Name.Denoting(WrittenName.of("Invoice", POS), DECLARED).denotes());
    }

    /** And there is no third answer for a reader below the pass to tell apart. */
    @Test
    void aNameNothingHasReadIsNotOneOfTheAnswers() {
        assertEquals(Set.of(Hir.Name.Denoting.class, Hir.Name.Unanswered.class),
                Set.of(Hir.Name.class.getPermittedSubclasses()));
    }
}
