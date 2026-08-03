package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.Type;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The two questions the inliner asks of a declared type — does it carry a collection, does it hold a
 * type variable — are asked of what the reference denotes, not of how it was spelled.
 *
 * <p>A reference a helper's own settling wrote carries its type and no surface text at all
 * ({@link Ast.TypeRef#of}), so a question read off the spelling answers no about every one of them.
 */
class ASettledTypeAnswersLikeAWrittenOneTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    /** {@code List<'a>} as the parser reads it. */
    private static Ast.TypeRef written() {
        return new Ast.TypeRef("List", new Ast.TypeRef("'a", null, POS), POS);
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

    @Test
    void aSettledCollectionIsFound() {
        assertTrue(HelperInliner.carriesCollection(Ast.TypeRef.of(Type.list(Type.INT), POS)));
        assertTrue(HelperInliner.carriesCollection(
                Ast.TypeRef.of(Type.option(Type.set(Type.INT)), POS)));
        assertFalse(HelperInliner.carriesCollection(Ast.TypeRef.of(Type.INT, POS)));
    }

    /** A written reference answers what it answered before, so the two readings agree. */
    @Test
    void aWrittenTypeAnswersAsItDid() {
        assertTrue(HelperInliner.mentionsTypeVar(written()));
        assertTrue(HelperInliner.carriesCollection(written()));
        assertFalse(HelperInliner.mentionsTypeVar(new Ast.TypeRef("Int", null, POS)));
        assertFalse(HelperInliner.carriesCollection(new Ast.TypeRef("Int", null, POS)));
    }
}
