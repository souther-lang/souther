package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.Type;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The question the inliner asks of a declared type — does it hold a type variable — is asked of what
 * the reference denotes, not of how it was spelled.
 *
 * <p>A reference a helper's own settling wrote carries its type and no surface text at all
 * ({@link Hir.TypeRef#of}), so a question read off the spelling answers no about every one of them.
 */
class ASettledTypeAnswersLikeAWrittenOneTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    @Test
    void aSettledTypeVariableIsFound() {
        assertTrue(HelperInliner.mentionsTypeVar(Hir.TypeRef.of(Type.list(Type.var("'a")), POS)));
        assertTrue(HelperInliner.mentionsTypeVar(Hir.TypeRef.of(Type.var("'a"), POS)));
        assertTrue(HelperInliner.mentionsTypeVar(
                Hir.TypeRef.of(Type.map(Type.STRING, Type.var("'v")), POS)));
    }

    @Test
    void aSettledTypeWithNoVariableIsNotFound() {
        assertFalse(HelperInliner.mentionsTypeVar(Hir.TypeRef.of(Type.list(Type.INT), POS)));
        assertFalse(HelperInliner.mentionsTypeVar(Hir.TypeRef.of(Type.INT, POS)));
    }

    /**
     * There is no reference here that resolution has not read.
     *
     * <p>The question this asks used to have a second answer — a reference still written, answered
     * off its characters, which is a second resolution: the same spelling means different things in
     * different modules and the reference no longer says which one it was written in. A written
     * reference is {@link souther.compiler.ast.Ast.TypeRef} now, and this operation cannot be
     * handed one, so the reading has nowhere left to happen.
     */
    @Test
    void everyReferenceHereCarriesWhatItStandsFor() {
        Hir.TypeRef settled = Hir.TypeRef.of(Type.list(Type.var("'a")), POS);

        assertNotNull(settled.denotes(), "a reference of this representation stands for a type");
    }
}
