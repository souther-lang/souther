package souther.program.api;

import souther.compiler.abort.AbortKind;
import souther.compiler.abort.AbortSet;
import souther.compiler.core.Core;
import souther.compiler.program.CheckedProgram;
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
 * What {@link CheckedProgram#constructionAborts} answers: what an ordinary construction of a
 * declared type can end without a value for, where the construction is not a site the program
 * holds — a value an output builds out of what a row states.
 *
 * <p>Asked first of a program that constructs none of the types it asks about, in a body or
 * anywhere else, so what is fixed is that the answer comes from the declarations and not from
 * whichever constructions the program happens to hold. Then of one that does construct them, where
 * the answer is the one each written construction is filed with.
 */
class AConstructionNoProgramHoldsAnswersWhatItCanEndWithTest {

    /** Declares the types and builds a value of none of them. */
    private static final String DECLARING = """
            module m

            import String ( length )

            data Plain = { n: Int }
            data Held = { n: Int }
                invariant n > 0
            data Code = String
                invariant length(value) > 0
            data Marker
            data Either = Plain | Held
            """;

    /** A type another module of the compile declares, with an invariant, and constructed nowhere. */
    private static final String UPSTREAM = """
            module up

            data Counted = { n: Int }
                invariant n >= 0
            """;

    /** The same types, and a value of each built in a body. */
    private static final String CONSTRUCTING = """
            module m exposing ( Plain, Held, Code, plain, held, code )

            import String ( length )

            data Plain = { n: Int }
            data Held = { n: Int }
                invariant n > 0
            data Code = String
                invariant length(value) > 0

            let plain = Plain { n = 1 }

            let held = Held { n = 1 }

            let code = Code("a")
            """;

    private static final CheckedProgram WITHOUT_CONSTRUCTIONS =
            CheckedProgram.of(List.of(DECLARING, UPSTREAM));

    @Test
    void aTypeWithAnInvariantAbortsOnItWhereNothingConstructsIt() {
        assertEquals(AbortSet.of(AbortKind.INVARIANT_NOT_HELD),
                WITHOUT_CONSTRUCTIONS.constructionAborts(declared("m", "Held")));
        assertEquals(AbortSet.of(AbortKind.INVARIANT_NOT_HELD),
                WITHOUT_CONSTRUCTIONS.constructionAborts(declared("m", "Code")));
        assertEquals(AbortSet.of(AbortKind.INVARIANT_NOT_HELD),
                WITHOUT_CONSTRUCTIONS.constructionAborts(declared("up", "Counted")));
    }

    @Test
    void aTypeWithoutOneEndsNothing() {
        assertEquals(AbortSet.NONE,
                WITHOUT_CONSTRUCTIONS.constructionAborts(declared("m", "Plain")));
    }

    /** Not answered as {@link AbortSet#NONE}: nothing constructs a unit or a sum of its own. */
    @Test
    void aDeclarationNotBuiltOutOfFieldsIsRefused() {
        assertThrows(IllegalArgumentException.class,
                () -> WITHOUT_CONSTRUCTIONS.constructionAborts(declared("m", "Marker")));
        assertThrows(IllegalArgumentException.class,
                () -> WITHOUT_CONSTRUCTIONS.constructionAborts(declared("m", "Either")));
    }

    @Test
    void aTypeNothingDeclaresIsRefused() {
        assertThrows(IllegalArgumentException.class,
                () -> WITHOUT_CONSTRUCTIONS.constructionAborts(declared("m", "Nowhere")));
    }

    /** The same answer a construction the program does hold is filed with. */
    @Test
    void theAnswerIsTheOneABodyConstructingTheSameTypeIsFiledWith() {
        CheckedProgram program = CheckedProgram.of(List.of(CONSTRUCTING));
        for (String each : List.of("plain", "held", "code")) {
            Core.Construct written = assertInstanceOf(Core.Construct.class,
                    program.module("m").value(new ValueName.Helper("m", each)).body());
            assertEquals(program.abortsAt(written), program.constructionAborts(written.typeName()),
                    each);
        }
    }

    private static TypeSymbol.AtModule declared(String module, String name) {
        return TypeSymbols.declared(new TypeKey(module, name));
    }
}
