package souther.compiler;

import souther.compiler.ast.Ast;
import souther.compiler.diag.SourcePos;

import org.junit.jupiter.api.Test;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * An argument list applies to the expression before it, not only to a name. What is applied is
 * decided by that expression, which is what {@code Ast.Apply} holds.
 *
 * <p>Souther's grammar is not newline sensitive — a leading `.` or operator continues the line above
 * — but an argument list is the one thing that cannot follow a line break. A block whose statement
 * ends in a list or a tuple is followed by a result expression that often opens with `(`, and
 * reading that as an application takes the block's result away. The standard library is written
 * that way, so the rule is written down here.
 */
class CompilePostfixApplicationTest {

    private static Map<?, ?> run(String source, Map<String, Object> in) throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(source),
                CompilePostfixApplicationTest.class.getClassLoader());
        Object behavior = loader.loadClass("demo.Go$Impl").getConstructor().newInstance();
        return (Map<?, ?>) Codecs.encode(loader, "demo.Out",
                Codecs.apply(behavior, Codecs.decoded(loader, "demo.In", in)));
    }

    /**
     * The one that exercises the whole path at once: a library name read as a value, a written block
     * it is chosen against, the choice made at run time, the result applied where it stands, the
     * synthetic binding that holds it, and the {@code Fn} the backend applies.
     */
    @Test
    void aChoiceBetweenAFunctionNameAndABlockIsAppliedWhereItStands() throws Exception {
        String src = """
                module demo

                data In = { s: String, flag: Bool }
                data Out = { t: String }

                behavior go : (i: In) -> Out constructs Out

                let go (i) = Out {
                    t = (if i.flag then String.trim else (s) -> String.append(s, "!"))(i.s)
                }
                """;

        assertEquals("a", run(src, Map.of("s", " a ", "flag", true)).get("t"));
        assertEquals("a!", run(src, Map.of("s", "a", "flag", false)).get("t"));
    }

    /** A function answered by an application is applied in turn. */
    @Test
    void anApplicationIsAppliedInTurn() throws Exception {
        Map<?, ?> out = run("""
                module demo

                data In = { n: Int }
                data Out = { m: Int }

                let bumpBy (k: Int) : (Int) -> Int = (x) -> x + k

                behavior go : (i: In) -> Out constructs Out

                let go (i) = Out { m = bumpBy(10)(i.n) }
                """, Map.of("n", 5L));

        assertEquals(15L, out.get("m"));
    }

    /**
     * The applied expression is worked out once and before any argument. Both sides construct, so
     * getting the order wrong is visible in what the behavior is permitted to build; getting the
     * count wrong would build twice.
     */
    @Test
    void theAppliedExpressionIsWorkedOutOnceAndFirst() throws Exception {
        Map<?, ?> out = run("""
                module demo

                data In = { n: Int }
                data Out = { m: Int }

                let pick (k: Int) : (Int) -> Int = (x) -> x * k

                behavior go : (i: In) -> Out constructs Out

                let go (i) = Out { m = pick(i.n + 1)(i.n + 2) }
                """, Map.of("n", 3L));

        assertEquals(20L, out.get("m"), "(3+1) * (3+2)");
    }

    /** A field is still taken off what an application answered. */
    @Test
    void aFieldIsTakenOffWhatAnApplicationAnswered() throws Exception {
        Map<?, ?> out = run("""
                module demo

                data Amount = Int
                data In = { n: Int }
                data Out = { m: Int }

                let amountOf (n: Int) = Amount(n)

                behavior go : (i: In) -> Out constructs Out, Amount

                let go (i) = Out { m = amountOf(i.n).value }
                """, Map.of("n", 7L));

        assertEquals(7L, out.get("m"));
    }

    /**
     * A line break ends the reach of an argument list. Without this the result of a block whose
     * previous statement ends in a list or a tuple is read as an application of it, and the block is
     * left with no result at all.
     */
    @Test
    void anArgumentListDoesNotReachAcrossALineBreak() throws Exception {
        Map<?, ?> out = run("""
                module demo

                data In = { n: Int }
                data Out = { m: Int }

                behavior go : (i: In) -> Out constructs Out

                let go (i) = {
                    let xs = [i.n, i.n]
                    (Out { m = List.length(xs) })
                }
                """, Map.of("n", 1L));

        assertEquals(2L, out.get("m"));
    }

    /** Applying something that is not a function is told so, whatever expression answered it. */
    @Test
    void applyingSomethingThatIsNotAFunctionIsRefused() {
        assertThrows(Exception.class, () -> Compiler.compile("""
                module demo

                data In = { n: Int }
                data Out = { m: Int }

                behavior go : (i: In) -> Out constructs Out

                let go (i) = Out { m = (i.n)(i.n) }
                """));
    }

    /** The list literal is a value, not something an argument list on the next line applies to. */
    @Test
    void aListLiteralFollowedByAParenthesisedResultKeepsBoth() throws Exception {
        Map<?, ?> out = run("""
                module demo

                data In = { n: Int }
                data Out = { m: Int }

                behavior go : (i: In) -> Out constructs Out

                let go (i) = {
                    let pair = (i.n, i.n)
                    let (a, b) = pair
                    Out { m = a + b }
                }
                """, Map.of("n", 4L));

        assertEquals(8L, out.get("m"));
    }

    /**
     * A line comment ends the line, so what follows it is a new expression — the same answer a bare
     * newline gives. Souther has no comment that stays inside a line, so there is no third case.
     */
    @Test
    void aLineCommentEndsTheReachOfAnArgumentList() throws Exception {
        Map<?, ?> out = run("""
                module demo

                data In = { n: Int }
                data Out = { m: Int }

                behavior go : (i: In) -> Out constructs Out

                let go (i) = {
                    let ys = [i.n]   // the list this walks
                    (Out { m = List.length(ys) })
                }
                """, Map.of("n", 3L));

        assertEquals(1L, out.get("m"));
    }

    /**
     * The shape the standard library is written in, which is what decided the rule: a statement
     * ending in a list, and a result opening with a parenthesis.
     */
    @Test
    void aStatementEndingInAListIsNotAppliedToTheResultBelowIt() throws Exception {
        Map<?, ?> out = run("""
                module demo

                data In = { n: Int }
                data Out = { m: Int }

                behavior go : (i: In) -> Out constructs Out

                let go (i) = {
                    let ys = [i.n] ++ [i.n]
                    (Out { m = List.length(ys) })
                }
                """, Map.of("n", 2L));

        assertEquals(2L, out.get("m"));
    }

    /** A field access still continues the line above, as it always has. */
    @Test
    void aFieldAccessStillReachesAcrossALineBreak() throws Exception {
        Map<?, ?> out = run("""
                module demo

                data Amount = Int
                data In = { n: Int }
                data Out = { m: Int }

                let amountOf (n: Int) = Amount(n)

                behavior go : (i: In) -> Out constructs Out, Amount

                let go (i) = Out { m = amountOf(i.n)
                    .value }
                """, Map.of("n", 9L));

        assertEquals(9L, out.get("m"));
    }

    /**
     * What an application applies is asked for as what it is. A reader keyed by name gets the miss
     * it wants; a reader that would do something else with the absence is handed nothing to mistake
     * for a name.
     */
    @Test
    void anApplicationSaysWhetherItAppliesAName() {
        SourcePos at = new SourcePos(1, 1);
        Ast.Apply named = new Ast.Apply("List.map", java.util.List.of(), at);
        Ast.Apply nameless = new Ast.Apply(new Ast.Block(java.util.List.of(),
                new Ast.IntLit(1, at), at), java.util.List.of(),
                souther.compiler.types.ConstructionOrigin.own(), at);

        assertTrue(named.appliesAName());
        assertEquals("List.map", named.written());
        assertEquals("List.map", named.namedCallee().orElseThrow().name());

        assertFalse(nameless.appliesAName());
        assertEquals("", nameless.written(), "a table keyed by name misses");
        assertTrue(nameless.namedCallee().isEmpty(), "and nothing is handed back to read");
    }
}
