package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.SourcePos;
import souther.compiler.meta.ModulePath;
import souther.compiler.types.TypeName;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * A cursor on a declaration's own name is on that declaration. The question was answered by
 * comparing the cursor against where the declaration starts — its {@code data} keyword — which is
 * not where its name is written, so the answer was there for a cursor on the keyword and absent for
 * one on the name.
 *
 * <p>What that cost is not visible from here: an editor asking this and getting nothing falls back
 * to matching by spelling, which answers, and answers about whatever else in the workspace is
 * spelled the same.
 */
class ADeclarationIsNamedWhereItsNameIsWrittenTest {

    private static final String ID = "m.sou";

    /** `data` starts at column 1 and `D` is written at column 6. */
    private static final String SOURCE = """
            module m

            data D = { v: Int }
            behavior f : (d: D) -> D
            let f (d) = d
            """;

    private static TypeName under(int line, int column) {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put(ID, SOURCE);
        return Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY).db()
                .ask(new Names.TypeAt(new SourcePos(line, column, ID))).value();
    }

    @Test
    void aCursorOnTheNameIsOnTheDeclaration() {
        assertEquals(new TypeName("m", "D"), under(3, 6));
    }

    @Test
    void aCursorJustPastTheNameIsStillOnIt() {
        assertEquals(new TypeName("m", "D"), under(3, 7));
    }

    @Test
    void aCursorOnTheKeywordIsNotOnTheName() {
        assertNull(under(3, 1), "`data` is not what the declaration is called");
    }

    @Test
    void aCursorOnAUseIsStillOnWhatTheUseDenotes() {
        assertEquals(new TypeName("m", "D"), under(4, 18));
    }
}
