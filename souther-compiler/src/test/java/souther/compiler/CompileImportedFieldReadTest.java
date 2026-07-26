package souther.compiler;

import souther.compiler.diag.CompileException;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Reading one field of an imported data needs that field's type in scope, not every field's. Typing
 * a field access resolved the owner's whole field map, so a module reading `breakdown.net` — an
 * `Int` — was made to import the type of a field it never touches, and the error carried the
 * *declaring* file's position, which rendered against the reading file pointed at an unrelated line
 * (issue #110).
 */
class CompileImportedFieldReadTest {

    private static final String UP = """
            module up exposing ( Rate, Box )
            data Rate = Decimal
            data Box =
                { n: Int
                , rate: Rate
                }
            """;

    @Test
    void readingAFieldDoesNotRequireASiblingFieldsTypeInScope() {
        Compiler.compileModules(List.of(UP, """
                module down
                import up ( Box )

                data Out = { doubled: Int }

                behavior twice : (b: Box) -> Out constructs Out
                let twice (b) = Out { doubled = b.n * 2 }
                """));
    }

    @Test
    void readingTheFieldWhoseTypeIsMissingStillReportsIt() {
        // the sibling is fine to leave out; the field actually read is not
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(UP, """
                        module down
                        import up ( Box )

                        data Out = { r: Rate }

                        behavior pick : (b: Box) -> Out constructs Out
                        let pick (b) = Out { r = b.rate }
                        """)));

        assertTrue(e.getMessage().contains("Rate"), e.getMessage());
    }

    @Test
    void aFieldTheDataDoesNotHaveIsStillRejected() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(UP, """
                        module down
                        import up ( Box )

                        data Out = { n: Int }

                        behavior pick : (b: Box) -> Out constructs Out
                        let pick (b) = Out { n = b.missing }
                        """)));

        assertTrue(e.getMessage().contains("missing"), e.getMessage());
    }

    private static final String SPREAD_UP = """
            module up exposing ( Rate, Common, Box )
            data Rate = Decimal
            data Common = { n: Int }
            data Box =
                { ...Common
                , rate: Rate
                }
            """;

    @Test
    void aFieldReachedThroughASpreadIsFoundWhenTheIncludedDataIsInScope() {
        Compiler.compileModules(List.of(SPREAD_UP, """
                module down
                import up ( Common, Box )

                data Out = { doubled: Int }

                behavior twice : (b: Box) -> Out constructs Out
                let twice (b) = Out { doubled = b.n * 2 }
                """));
    }

    /** The remaining half of the same over-reach, recorded rather than fixed: a field spread in from
     *  another data still needs that data in scope, because the reader walks the includes through its
     *  own symbol table and cannot see a name it did not import. Answering it needs the declaring
     *  module's symbols, which the field-access check does not have. */
    @Test
    void aSpreadInFieldStillNeedsTheIncludedDataImported() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(SPREAD_UP, """
                        module down
                        import up ( Box )

                        data Out = { doubled: Int }

                        behavior twice : (b: Box) -> Out constructs Out
                        let twice (b) = Out { doubled = b.n * 2 }
                        """)));

        assertTrue(e.getMessage().contains("n"), e.getMessage());
    }
}
