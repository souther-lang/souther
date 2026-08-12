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

    /** The other half of the same reach: the spread is written in `up`, so `up` is where its name
     *  is resolved. Importing `Box` is enough to read a field spread into it — the reader no longer
     *  needs `Common` in scope as well. */
    @Test
    void aFieldSpreadInFromAnotherDataNeedsOnlyTheDataItIsReadFrom() {
        Compiler.compileModules(List.of(SPREAD_UP, """
                module down
                import up ( Box )

                data Out = { doubled: Int }

                behavior twice : (b: Box) -> Out constructs Out
                let twice (b) = Out { doubled = b.n * 2 }
                """));
    }
}
