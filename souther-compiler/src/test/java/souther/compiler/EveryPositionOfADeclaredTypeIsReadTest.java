package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.query.Compilation;

import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * A variable in a declared type is a hole at its own position, and states nothing about any other.
 *
 * <p>{@code List<'a>} says the value is a list; {@code Map<String, 'a>} says it is a map with String
 * keys; {@code ('a) -> String} says the function answers a String whatever it is given. An argument
 * is held to all of that, and free only where the variable stands.
 *
 * <p>Held whatever else is true of the call, which is what these rows vary. Whether the callee's body
 * ever reads the parameter, whether it applies the function it was given, whether the lambda reads
 * what it was handed, whether the argument was written as a lambda or as a name — none of them is a
 * question about what the declaration says, so none of them changes the answer.
 */
class EveryPositionOfADeclaredTypeIsReadTest {

    /**
     * One reading of one declared position. {@code declares} is what the callee writes of the
     * parameter, {@code fits} an argument the declaration admits and {@code refused} one it does
     * not — the pair being the point, since a hole admits so much that the admitting half alone
     * would say nothing.
     */
    record Row(String what, String declares, String uses, String fits, String refused) {

        @Override
        public String toString() {
            return what;
        }
    }

    private static final String READS = "let said = f(1)";

    private static List<Row> rows() {
        return List.of(
                new Row("a value the callee never reads", "x: Int", "", "1", "\"s\""),
                new Row("a list the callee never reads", "xs: List<'a>", "", "[ 1 ]", "1"),
                new Row("a map whose key the declaration names", "m: Map<String, 'a>", "",
                        "Map.empty", "[ 1 ]"),
                new Row("a function the callee never applies", "f: ('a) -> Bool", "",
                        "(x) -> x > 1", "(x) -> x + 1"),
                new Row("a function the callee applies", "f: (Int) -> String", READS,
                        "(n) -> \"s\"", "(n) -> n"),
                new Row("a named function the callee applies", "f: (Int) -> String", READS,
                        "labelled", "unlabelled"),
                new Row("a function applied, at a position left open", "f: ('a) -> String", READS,
                        "(x) -> \"s\"", "(x) -> x + 1"),
                new Row("a function whose parameter the lambda never reads", "f: ('a) -> String",
                        READS, "(x) -> \"s\"", "(x) -> 1"),
                new Row("a function whose parameter nothing determines", "f: ('a) -> String", READS,
                        "(x) -> { let ignored = x\n        \"s\" }",
                        "(x) -> { let ignored = x\n        1 }"),
                new Row("a result stating only its constructor", "f: ('a) -> List<'b>", READS,
                        "(x) -> [ 1 ]", "(x) -> 1"));
    }

    private static String module(Row row, String argument) {
        return """
                module souther.gen
                let labelled (n: Int) = "s"
                let unlabelled (n: Int) = n
                let use (%s) = {
                    %s
                    true
                }
                let call = use(%s)
                """.formatted(row.declares(), row.uses(), argument);
    }

    private static CompileException failure(String source) {
        Compilation compilation = Compilation.ofCoreSource(source);
        compilation.answerEverything();
        return compilation.firstError(compilation.db().allReports());
    }

    @ParameterizedTest(name = "{0}")
    @MethodSource("rows")
    void whatTheDeclarationAdmitsIsAccepted(Row row) {
        assertNull(failure(module(row, row.fits())), "the declaration admits this argument");
    }

    @ParameterizedTest(name = "{0}")
    @MethodSource("rows")
    void whatItDoesNotAdmitIsRefused(Row row) {
        CompileException e = failure(module(row, row.refused()));
        assertEquals(true, e != null, "the declaration does not admit this argument");
    }

    /**
     * The same again with no call at all: a helper handing its own function parameter on is read
     * where it is written, not only where a lambda reaches it.
     */
    @ParameterizedTest(name = "{0}")
    @MethodSource("relayed")
    void aFunctionHandedOnIsReadWhereTheHelperIsWritten(Row row) {
        String relaying = """
                module souther.gen
                let inner (g: (Int) -> String) = {
                    %s
                    true
                }
                let use (f: (Int) -> %%s) = inner(f)
                """.formatted(row.uses());
        assertNull(failure(relaying.formatted("String")), "both boundaries declare the same thing");
        assertEquals(true, failure(relaying.formatted("Int")) != null,
                "the boundary it is handed on to declares something else");
    }

    /**
     * A function handed on to another function parameter is read at the boundary it arrives at.
     *
     * <p>Each boundary states its own type, and what one declares of what it takes is not what the
     * function was declared as where it came in. Here the two disagree and only the second says so:
     * {@code use} takes a function answering an Int and hands it to {@code inner}, which declares
     * one answering a String.
     */
    @ParameterizedTest(name = "{0}")
    @MethodSource("relayed")
    void aFunctionHandedOnIsReadAtTheBoundaryItArrivesAt(Row row) {
        String relaying = """
                module souther.gen
                let inner (g: (Int) -> String) = {
                    %s
                    true
                }
                let use (f: (Int) -> %%s) = inner(f)
                let call = use(%%s)
                """.formatted(row.uses());
        assertNull(failure(relaying.formatted("String", row.fits())),
                "both boundaries declare what this answers");
        assertEquals(true, failure(relaying.formatted("Int", row.refused())) != null,
                "the boundary it is handed on to declares something else");
    }

    private static List<Row> relayed() {
        return List.of(
                new Row("handed on, and applied", "", "let said = g(1)", "(x) -> \"s\"", "(x) -> x"),
                new Row("handed on, never applied", "", "", "(x) -> \"s\"", "(x) -> x"));
    }
}
