package souther.compiler;

import souther.compiler.diag.msg.ParseMessage;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * No type position answers a written type form with the delimiter it wanted next.
 *
 * <p>This is the invariant #522 was one cell of. A position that reads a narrow type production
 * refuses some forms in the grammar, which is a decision about the language; what does not follow
 * from it is that the refusal has to be reported as a missing `}` or `>`. Where nothing recognizes
 * the form, delimiter recovery is all that is left, and what the author reached for is gone from
 * the answer — so the same misconception got a repair in one position and a token complaint in
 * another, decided by which production the position happened to call.
 *
 * <p>So the quantifier is over every type position crossed with every type form, and the question
 * asked of each is only whether the answer is about the form. Which code it carries, and whether it
 * is refused at all, is each position's own business and is held elsewhere. Some cells here fail on
 * the value rather than the type — a helper's declared return given a value of another type — and
 * that is fine: those are answers about something, which is the whole of what this asks.
 *
 * <p>It is worth knowing this is not vacuous. Against the compiler as it stood before the
 * recognition was added, five of these cells answered with a delimiter: a `|` on a data field, and
 * a `|` and a `?` in each of a type argument and a tuple's member.
 */
class NoTypePositionAnswersWithADelimiterTest {

    /** Where a type is written, as a template the form is substituted into. */
    private static final List<String> POSITIONS = List.of(
            "data Hold = { x: %s }",
            "data Hold = %s",
            "behavior go : (i: %s) -> A\n    constructs A\n\nlet go (i) = A { a = 1 }",
            "behavior go : (i: Out) -> %s\n    constructs A\n\nlet go (i) = A { a = 1 }",
            "let aux (h: %s) = 1",
            "let aux (n: Int) : %s = n",
            "let aux (h: List<%s>) = 1",
            "let aux (h: (%s, Int)) = 1",
            "let aux (f: (%s) -> Int) = 1",
            "let aux (f: (Int) -> %s) = 1");

    /** Every form the type position admits somewhere, including the ones some positions refuse. */
    private static final List<String> FORMS =
            List.of("A | B", "Int?", "(Int, Int)", "(Int) -> Int", "List<Int>", "A");

    private static final String PRELUDE = """
            module demo

            data A = { a: Int }
            data B = { b: Int }
            data Out = { v: Int }

            """;

    private static final String IMPL = """


            behavior run : (i: Out) -> Out
                constructs Out

            let run (i) = Out { v = 1 }
            """;

    /** Whether the answer names the delimiter the reading stopped at rather than what was written. */
    private static boolean isDelimiterComplaint(Diagnostic d) {
        return d.said() instanceof ParseMessage.ADeclarationExpectedSomethingElse
                || d.said() instanceof ParseMessage.AnExpressionExpectedSomethingElse
                || d.said() instanceof ParseMessage.APatternExpectedSomethingElse
                || d.said() instanceof ParseMessage.AnExampleExpectedSomethingElse;
    }

    @Test
    void everyTypeFormIsAnsweredAboutWhereverItIsWritten() {
        List<String> bare = new ArrayList<>();
        int refused = 0;
        for (String position : POSITIONS) {
            for (String form : FORMS) {
                String src = PRELUDE + String.format(position, form) + IMPL;
                try {
                    Compiler.compile(src);
                } catch (CompileException e) {
                    refused++;
                    if (isDelimiterComplaint(e.diagnostic())) {
                        bare.add(String.format(position, form).split("\n")[0]
                                + "  ->  " + e.diagnostic().code());
                    }
                }
            }
        }
        assertEquals(List.of(), bare,
                "a type position answered a written type form with the delimiter it wanted next");
        // Guards the quantifier: if every cell started compiling, the loop above would assert nothing.
        assertTrue(refused >= 20, "expected the refusing cells to still refuse, got " + refused);
    }
}
