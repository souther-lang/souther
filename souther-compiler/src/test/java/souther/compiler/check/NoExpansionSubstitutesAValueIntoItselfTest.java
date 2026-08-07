package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.diag.CompileException;
import souther.compiler.frontend.CstFrontend;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The expansion refuses to substitute a value it is already substituting, whoever asked it to.
 *
 * <p>Which modules are well founded is {@link ValueCycles}' answer and it is asked of the module,
 * before anything expands a body of it — that is the rule the author is told about. This is a
 * different statement about a different thing: the expansion is an algorithm, and an algorithm handed
 * an input its precondition rules out should answer wrongly and say so rather than descend until the
 * stack runs out. What comes back from a stack that ran out is a report about an expression nesting
 * too deeply, which is about nothing the author wrote, and it is caught only at the compiler's outer
 * boundary — by which point which question was being answered is gone.
 *
 * <p>So this asks for the failure directly, with an inliner built the way a caller outside the query
 * layer builds one: nothing here goes through {@code Shapes.Expandable}, which is the point.
 */
class NoExpansionSubstitutesAValueIntoItselfTest {

    private static final String HEAD = """
            module demo

            data In = { n: Int }
            data Out = { n: Int }

            """;

    private static final String TAIL = """

            let use (n: Int) : Int = n + seed

            behavior go : (i: In) -> Out
                constructs Out
            let go (i) = Out { n = use(i.n) }
            """;

    private static HelperInliner inlinerFor(String source) {
        Ast.Module parsed = CstFrontend.parse(source);
        return HelperInliner.forModule(Resolve.module(parsed, Symbols.of(parsed)));
    }

    private static Ast.Expr expand(HelperInliner inliner, String helper) {
        return inliner.inline(inliner.emits().get(helper).writtenBody(), inliner.bodyOf(helper));
    }

    private static Ast.Expr expand(String source, String helper) {
        return expand(inlinerFor(source), helper);
    }

    @Test
    void aValueDefinedAsItselfIsRefusedRatherThanSubstitutedForever() {
        ExpansionCycle refused = assertThrows(ExpansionCycle.class,
                () -> expand(HEAD + "let seed = seed" + TAIL, "use"));

        assertTrue(refused.getMessage().contains("seed"),
                "the failure names the value it was substituting: " + refused.getMessage());
    }

    @Test
    void aValueReachingItselfThroughAHelperIsRefusedToo() {
        String source = HEAD + """
                let seed = twice(1)

                let twice (n: Int) : Int = n * seed
                """ + TAIL;

        assertThrows(ExpansionCycle.class, () -> expand(source, "use"));
    }

    /**
     * A spread names a value where an expression cannot stand, so the substitution happens at the
     * construction rather than at the name — a second place to reach a value's body, and the same
     * failure when it is the body being reached from.
     */
    @Test
    void aValueSpreadIntoItsOwnConstructionIsRefusedToo() {
        String source = """
                module demo

                data In = { n: Int }
                data Out = { n: Int }
                data D = { n: Int }

                let seed = D { ...seed }

                let use (d: D) : D = seed

                behavior go : (i: In) -> Out
                    constructs Out
                let go (i) = Out { n = i.n }
                """;

        assertThrows(ExpansionCycle.class, () -> expand(source, "use"));
    }

    /**
     * One value substituted twice is not a value substituted into itself. The two substitutions are
     * beside each other rather than one inside the other, and an expansion that recorded every value
     * it had ever substituted would refuse the second.
     */
    @Test
    void theSameValueTwiceInOneBodyIsNotReEntry() {
        String source = HEAD + """
                let seed = 1
                """ + """

                let use (n: Int) : Int = n + seed + seed

                behavior go : (i: In) -> Out
                    constructs Out
                let go (i) = Out { n = use(i.n) }
                """;

        assertDoesNotThrow(() -> expand(source, "use"));
    }

    /**
     * A caller records a refusal and hands the next body to the same pass, so what a substitution
     * that did not finish left behind is read by the body after it. A value it was standing in when
     * it was refused is not a value it is still standing in: left there, the next body to name that
     * value would be told it reaches itself, which is a report about the wrong thing entirely and
     * about a module with nothing of the kind wrong with it.
     */
    @Test
    void aSubstitutionRefusedPartwayIsNotStillStandingForTheNextBody() {
        HelperInliner inliner = inlinerFor("""
                module demo

                data In = { n: Int }
                data Out = { n: Int }

                let applyTwice (f: (Int) -> Int, n: Int) : Int = f(n, n)

                let bad = applyTwice((x) -> x + 1, 1)

                let use (n: Int) : Int = n + bad
                let again (n: Int) : Int = n + bad

                behavior go : (i: In) -> Out
                    constructs Out
                let go (i) = Out { n = use(i.n) + again(i.n) }
                """);
        assertThrows(CompileException.class, () -> expand(inliner, "use"),
                "the lambda takes one argument and is handed two");

        assertThrows(CompileException.class, () -> expand(inliner, "again"),
                "the second body is refused for what is wrong with it, not for reaching a value the"
                        + " expansion was left standing in");
    }
}
