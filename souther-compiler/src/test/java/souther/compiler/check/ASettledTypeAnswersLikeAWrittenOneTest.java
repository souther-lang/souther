package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.Type;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The question the inliner asks of a declared type — does it hold a type variable — is asked of what
 * the reference denotes, not of how it was spelled.
 *
 * <p>A reference a helper's own settling wrote carries its type and no surface text at all
 * ({@link Ast.TypeRef#of}), so a question read off the spelling answers no about every one of them.
 */
class ASettledTypeAnswersLikeAWrittenOneTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    /** {@code List<'a>} as the parser reads it, before resolution has said what it stands for. */
    private static Ast.TypeRef written() {
        return Ast.TypeRef.written("List", Ast.TypeRef.written("'a", null, POS), POS);
    }

    @Test
    void aSettledTypeVariableIsFound() {
        assertTrue(HelperInliner.mentionsTypeVar(Ast.TypeRef.of(Type.list(Type.var("'a")), POS)));
        assertTrue(HelperInliner.mentionsTypeVar(Ast.TypeRef.of(Type.var("'a"), POS)));
        assertTrue(HelperInliner.mentionsTypeVar(
                Ast.TypeRef.of(Type.map(Type.STRING, Type.var("'v")), POS)));
    }

    @Test
    void aSettledTypeWithNoVariableIsNotFound() {
        assertFalse(HelperInliner.mentionsTypeVar(Ast.TypeRef.of(Type.list(Type.INT), POS)));
        assertFalse(HelperInliner.mentionsTypeVar(Ast.TypeRef.of(Type.INT, POS)));
    }

    /**
     * A reference resolution has not read is refused rather than answered off its spelling.
     *
     * <p>This runs after resolution, so a reference still {@link Ast.TypeRef.Written} here is a
     * fault in the compiler. Answering it from the characters — {@code 'a} begins with a quote, so
     * say yes — is what the reading used to do, and it is a second resolution: the same spelling
     * means different things in different modules, and the reference no longer says which one it
     * was written in.
     */
    @Test
    void aTypeNothingHasReadIsRefused() {
        assertThrows(IllegalStateException.class, () -> HelperInliner.mentionsTypeVar(written()));
        assertThrows(IllegalStateException.class,
                () -> HelperInliner.mentionsTypeVar(Ast.TypeRef.written("Int", null, POS)));
    }
}
