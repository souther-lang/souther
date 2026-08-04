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

    /**
     * A variable written twice in one declaration is one variable, at the boundary as everywhere
     * else. {@code ('a) -> 'a} is a function answering what it was given, and neither position says
     * that on its own — so a boundary that read each position separately would admit a function
     * taking an Int and answering a String, which is the one thing the declaration refuses.
     *
     * <p>Both declarations at the boundary are read this way, whichever of them wrote the variable.
     */
    @ParameterizedTest(name = "{0}")
    @MethodSource("related")
    void aVariableWrittenTwiceIsOneVariableAtABoundaryToo(Row row) {
        String relaying = """
                module souther.gen
                let inner (g: %s) = true
                let use (f: %%s) = inner(f)
                """.formatted(row.declares());
        assertNull(failure(relaying.formatted(row.fits())), "the two positions agree");
        assertEquals(true, failure(relaying.formatted(row.refused())) != null,
                "one variable read at two types");
    }

    private static List<Row> related() {
        return List.of(
                new Row("the receiving declaration writes it twice", "('a) -> 'a", "",
                        "(Int) -> Int", "(Int) -> String"),
                new Row("the arriving declaration writes it twice", "(Int) -> String", "",
                        "('a) -> String", "('a) -> 'a"));
    }

    /**
     * What a function argument says about a variable is what that variable is everywhere else the
     * signature wrote it.
     *
     * <p>{@code (f: ('a) -> Bool): List<'a>} answers a list of what the function takes, so the
     * function is what decides the result — and a call site expecting a list of something else is
     * refused for that, rather than the result quietly taking what the position wanted. A signature
     * is one statement, and a boundary reading is a reading of it, not a question of its own.
     */
    @ParameterizedTest(name = "{0}")
    @MethodSource("deciding")
    void whatAFunctionArgumentSaysReachesTheRestOfTheSignature(Row row) {
        String source = """
                module souther.gen
                let emptyFrom (f: ('a) -> Bool): List<'a> = []
                let positive (n: Int) = n > 0
                let taking (xs: List<%%s>) = true
                %s
                """.formatted(row.declares());
        assertNull(failure(source.formatted("Int")), "the function says the list holds Ints");
        assertEquals(true, failure(source.formatted("String")) != null,
                "and the position wanting Strings does not make it so");
    }

    private static List<Row> deciding() {
        return List.of(
                new Row("a named function", "let call = taking(emptyFrom(positive))", "", "", ""),
                new Row("a function handed on",
                        "let relay (g: (Int) -> Bool) = emptyFrom(g)\n"
                                + "let call (g: (Int) -> Bool) = taking(relay(g))", "", "", ""));
    }
}
