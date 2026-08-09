package souther.compiler;

import souther.compiler.diag.msg.ParseMessage;
import souther.compiler.diag.msg.TypeMessage;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A position that reads the narrow type production answers about the form the author wrote.
 *
 * <p>A data field, a type argument and a tuple's member read a narrower production than a behavior's
 * parameter does, so an anonymous union is not a form any of the three is written in. That is a
 * decision about the language and it stands. What did not stand was its consequence for a reader: a form the
 * production never built could not be named by anything downstream, so a `|` on a field was
 * reported as a missing `}` and a `?` inside a `List` as a missing `>` — the token the parser
 * wanted, about text the author did not write.
 *
 * <p>So each forbidden continuation is recognized where it stands, ahead of the delimiter recovery
 * that would erase it. The tests here hold both halves: the recognition, and that nothing was
 * widened to get it — the same file with the form written correctly still compiles, and the
 * positions that already answered by form still do.
 */
class ANarrowTypePositionAnswersByFormTest {

    private static Diagnostic diagnosticOf(String src) {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        return e.diagnostic();
    }

    private static final String CASES = """
            module demo
            data A = { a: Int }
            data B = { b: Int }
            data Out = { v: Int }
            """;

    private static final String IMPL = """
            behavior run : (i: Out) -> Out constructs Out
            let run (i) = Out { v = 1 }
            """;

    @Test
    void aUnionOnAFieldNamesTheFieldAndTheRepair() {
        Diagnostic d = diagnosticOf(CASES + "data Holder = { ticket: A | B }\n" + IMPL);
        assertEquals("E2307", d.code());
        assertInstanceOf(ParseMessage.AFieldTypeIsNotAnAnonymousUnion.class, d.said());
        assertEquals("ticket", d.values().get("field"));
    }

    @Test
    void aUnionInATypeArgumentIsNamed() {
        Diagnostic d = diagnosticOf(CASES + "let aux (xs: List<A | B>) = 1\n" + IMPL);
        assertEquals("E2307", d.code());
        assertInstanceOf(ParseMessage.AnAnonymousUnionIsNotWrittenInsideAnotherType.class, d.said());
    }

    @Test
    void aUnionInATupleMemberIsNamed() {
        Diagnostic d = diagnosticOf(CASES + "let aux (t: (A | B, Int)) = 1\n" + IMPL);
        assertEquals("E2307", d.code());
        assertInstanceOf(ParseMessage.AnAnonymousUnionIsNotWrittenInsideAnotherType.class, d.said());
    }

    @Test
    void anOptionalInATypeArgumentIsNamed() {
        Diagnostic d = diagnosticOf(CASES + "let aux (xs: List<Int?>) = 1\n" + IMPL);
        assertEquals("E2308", d.code());
        assertInstanceOf(ParseMessage.AnOptionalIsNotWrittenInsideAnotherType.class, d.said());
    }

    @Test
    void anOptionalInATupleMemberIsNamed() {
        Diagnostic d = diagnosticOf(CASES + "let aux (t: (Int?, Int)) = 1\n" + IMPL);
        assertEquals("E2308", d.code());
        assertInstanceOf(ParseMessage.AnOptionalIsNotWrittenInsideAnotherType.class, d.said());
    }

    // The rule this code names is not the one E1402 names, and this is what tells them apart: E1402
    // refuses a `?` a user model writes where the core may write one, and the core writes `'b?` on a
    // function type's result. Inside another type there is nothing to be privileged about — the
    // production reads no `?` for anyone — so the reserved namespace is answered the same.
    @Test
    void anOptionalInsideATypeIsNotACorePrivilege() {
        Diagnostic d = diagnosticOf("""
                module souther.probe
                data Out = { v: Int }
                let aux (xs: List<Int?>) = 1
                behavior run : (i: Out) -> Out constructs Out
                let run (i) = Out { v = 1 }
                """);
        assertEquals("E2308", d.code());
        assertInstanceOf(ParseMessage.AnOptionalIsNotWrittenInsideAnotherType.class, d.said());
    }

    // The two positions that already answered by form still do, from the tiers they always did: a
    // parameter builds its union and the boundary refuses it, and a `?` outside a field in a whole
    // type is read and refused by the core-privilege rule.
    @Test
    void aParameterStillAnswersFromTheBoundary() {
        Diagnostic d = diagnosticOf(CASES + """
                behavior go : (t: A | B) -> Out constructs Out
                let go (t) = Out { v = 1 }
                """ + IMPL);
        assertEquals("E1312", d.code());
        assertInstanceOf(TypeMessage.AParameterIsAnAnonymousUnion.class, d.said());
    }

    @Test
    void anOptionalInAWholeTypeStillAnswersFromTheCoreRule() {
        Diagnostic d = diagnosticOf(CASES + "let aux (h: Int?) = 1\n" + IMPL);
        assertEquals("E1402", d.code());
        assertInstanceOf(ParseMessage.AnOptionalIsOnlyWrittenOnAFieldOrInTheCore.class, d.said());
    }

    // Nothing was widened. What each of these positions takes is what it took before, and the forms
    // that were always written there are still read: a `?` on a field, an `Option` as a type argument
    // and as a tuple's member, and a named type in all three.
    @Test
    void theFormsThesePositionsTakeStillCompile() {
        Compiler.compile("""
                module demo
                data A = { a: Int }
                data Holder = { x: Int?, one: A }
                data Out = { v: Int }
                let aux (xs: List<Option<Int>>, t: (Option<Int>, A)) = 1
                behavior run : (i: Out) -> Out constructs Out
                let run (i) = Out { v = 1 }
                """);
    }
}
