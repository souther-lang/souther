package souther.compiler.ast;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.SourcePos;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A name handed to a tree as text is canonical in it, whether or not it is written anywhere: what
 * hands it is not told apart by its type, so a name no one wrote is canonicalized as a spelling is
 * ({@link WrittenName#synthetic}).
 */
class ANameIsCanonicalHoweverATreeIsHandedItTest {

    /** か + a combining voiced sound mark. */
    private static final String DECOMPOSED = "が";
    /** The same kana as one code point. */
    private static final String CANONICAL = "が";

    private static final SourcePos AT = new SourcePos(1, 1);

    @Test
    void aNameOnAnImportListIs() {
        assertEquals(CANONICAL, new Ast.ImportedName(DECOMPOSED, null).text());
        assertEquals(CANONICAL, new Ast.ImportedName(DECOMPOSED, AT).text());
        assertEquals(CANONICAL, new Hir.ImportedName(DECOMPOSED, null).text());
        assertEquals(CANONICAL, new Hir.ImportedName(DECOMPOSED, AT).text());
    }

    @Test
    void aNameAPassWritesIs() {
        assertEquals(CANONICAL, WrittenName.synthetic(DECOMPOSED, AT).canonical());
        assertEquals(CANONICAL, new Ast.UnitData(DECOMPOSED, "m", AT).written().canonical());
        assertEquals(CANONICAL, new Ast.Field(DECOMPOSED, null, AT).name());
        assertEquals(CANONICAL, Ast.Binder.desugared(DECOMPOSED, AT).name());
        assertEquals(CANONICAL, new Hir.FieldInit(DECOMPOSED, null, AT).name());
    }
}
