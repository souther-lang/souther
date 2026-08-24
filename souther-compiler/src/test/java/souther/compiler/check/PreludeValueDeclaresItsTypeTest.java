package souther.compiler.check;

import souther.compiler.stdlib.Stdlib;
import souther.compiler.ast.Hir;
import souther.compiler.ast.WrittenName;
import souther.compiler.diag.SourcePos;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A zero-parameter prelude declaration is a value whose type only its signature can answer:
 * {@code CallElaborator.libraryValue} reads the signature's result with no call whose arguments
 * could pin it. So a shipped value that writes no return type is refused when the library is
 * loaded, rather than filed as an entry whose type nothing states and read as a null.
 */
class PreludeValueDeclaresItsTypeTest {

    @Test
    void aValueWithoutAWrittenTypeIsRefusedAtLoad() {
        SourcePos at = new SourcePos(1, 1);
        Hir.FnDef value = new Hir.FnDef(WrittenName.synthetic("someValue", at), "souther.list",
                List.of(), null, new Hir.FnBody.Written(new Hir.IntLit(0, at, null)), at);

        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> souther.compiler.check.StdlibLoader.signatureOf(value, "List.someValue"));
        assertTrue(refused.getMessage().contains("List.someValue"));
    }

    @Test
    void everyShippedValueStatesItsType() {
        for (Stdlib.Entry entry : souther.compiler.DefaultStdlib.get().entries().values()) {
            if (entry.declaration().params().isEmpty()) {
                assertNotNull(entry.signature().result(),
                        "`" + entry.declaration().name() + "` is a value with no stated type");
            }
        }
    }
}
