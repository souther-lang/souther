package souther.compiler;

import souther.compiler.ast.Ast;
import souther.compiler.check.Symbols;
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
        Ast.FnDef value = new Ast.FnDef("someValue", List.of(), null,
                new Ast.FnBody.Written(new Ast.IntLit(0, at)), at);

        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> Prelude.signatureOf(value, "List.someValue", Symbols.none()));
        assertTrue(refused.getMessage().contains("List.someValue"));
    }

    @Test
    void everyShippedValueStatesItsType() {
        for (Prelude.PreludeEntry entry : Prelude.entries().values()) {
            if (entry.declaration().params().isEmpty()) {
                assertNotNull(entry.signature().result(),
                        "`" + entry.declaration().name() + "` is a value with no stated type");
            }
        }
    }
}
