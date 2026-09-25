package souther.compiler.program;

import souther.compiler.abort.AbortKind;
import souther.compiler.abort.AbortSet;
import souther.compiler.core.Core;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A construction an output builds out of something other than a body — what a row states — is one
 * no program holds as a site, and what it can end without a value for is asked of its type instead.
 * The answer is the one a construction of the same type written in a body is filed with, so a value
 * a row states and the same value a body builds cannot be told to end differently.
 */
class AConstructionNoProgramHoldsAbortsAsOneItHoldsTest {

    private static final String MODULE = """
            module m exposing ( Plain, Held, Code, plain, held, code )

            import String ( length )

            data Plain = { n: Int }
            data Held = { n: Int }
                invariant n > 0
            data Code = String
                invariant length(value) > 0
            data Marker

            let plain = Plain { n = 1 }

            let held = Held { n = 1 }

            let code = Code("a")
            """;

    private static final CheckedProgram PROGRAM = CheckedProgram.of(List.of(MODULE));

    @Test
    void aTypeWithAnInvariantAbortsOnItAndOneWithoutEndsNothing() {
        assertEquals(AbortSet.of(AbortKind.INVARIANT_NOT_HELD),
                PROGRAM.constructionAborts(declared("Held")));
        assertEquals(AbortSet.of(AbortKind.INVARIANT_NOT_HELD),
                PROGRAM.constructionAborts(declared("Code")));
        assertEquals(AbortSet.NONE, PROGRAM.constructionAborts(declared("Plain")));
    }

    /** The same answer a construction the program does hold is filed with. */
    @Test
    void theAnswerIsTheOneABodyConstructingTheSameTypeIsFiledWith() {
        for (String each : List.of("plain", "held", "code")) {
            Core.Construct written = assertInstanceOf(Core.Construct.class,
                    PROGRAM.module("m").value(new ValueName.Helper("m", each)).body());
            assertEquals(PROGRAM.abortsAt(written), PROGRAM.constructionAborts(written.typeName()),
                    each);
        }
    }

    @Test
    void aDeclarationNotBuiltOutOfFieldsIsRefused() {
        assertThrows(IllegalArgumentException.class,
                () -> PROGRAM.constructionAborts(declared("Marker")));
    }

    @Test
    void aTypeNothingDeclaresIsRefused() {
        assertThrows(IllegalArgumentException.class,
                () -> PROGRAM.constructionAborts(declared("Nowhere")));
    }

    private static TypeSymbol.AtModule declared(String name) {
        return TypeSymbols.declared(new TypeKey("m", name));
    }
}
