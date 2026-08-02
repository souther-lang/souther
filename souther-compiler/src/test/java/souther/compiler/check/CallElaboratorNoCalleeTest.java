package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.TypeName;
import souther.compiler.types.ConstructionOrigin;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A call this module has no callee for is answered by what resolution said the name is. Every answer
 * it can give by this point is something — a name it could not place is thrown out earlier — so no
 * answer here may be "not a behavior or a builtin", which was said of a behavior, of a type and of a
 * binding alike and sent authors after typos they had not made.
 *
 * <p>Asked of {@code noCallee} directly rather than of a program, because that is what the rule is
 * about: the two classifications an author can write into are reachable from a source, and the rest
 * are reachable only when some earlier pass failed to expand what it should have. Compiling a program
 * to reach them would be compiling a compiler bug.
 */
class CallElaboratorNoCalleeTest {

    private static final SourcePos AT = new SourcePos(7, 3);

    private static RuntimeException answerFor(ValueName denotes) {
        return CallElaborator.noCallee(
                new Ast.Apply("f", denotes, List.of(new Ast.IntLit(1, AT)),
                        ConstructionOrigin.own(), AT));
    }

    /** A behavior named from a helper `let` or a `>->` composition, neither of which reaches one. */
    @Test
    void aBehaviorIsToldItIsABehavior() {
        RuntimeException e = answerFor(new ValueName.Behavior("m", "f"));
        assertEquals("E1401", assertInstanceOf(CompileException.class, e).code());
        assertEquals("e1401.behavior", ((CompileException) e).diagnostic().messageKey());
    }

    /**
     * A type applied to an argument is a construction, and every place one is allowed rewrites it
     * before the check reads it. Unreachable from a source once the rewrite covers every place an
     * expression is written — which is the point of holding the arm: the day a place is added and the
     * rewrite is not, the author is told a construction was written somewhere it cannot be, rather
     * than that their own type is not a behavior.
     */
    @Test
    void aTypeIsToldItConstructs() {
        RuntimeException e = answerFor(
                new ValueName.OfType("Yen", new TypeName("m", "Yen"), null));
        CompileException c = assertInstanceOf(CompileException.class, e);
        assertEquals("check.construct.position", c.diagnostic().messageKey());
        assertEquals(List.of("Yen"), List.of(c.diagnostic().args()));
    }

    /**
     * A binding applied to arguments, whose type here is not a function. Either it is not one — a
     * value applied as though it were — or it has no type yet, which is what an inference probe sees
     * when it types a body before the binding it asks about has one and reads the report to find out.
     * One sentence answers both: at the point of the report, this name is not a function here.
     */
    @Test
    void aBindingIsToldItIsNotAFunction() {
        RuntimeException e = answerFor(new ValueName.Local("f",
                new BindingId(new BindingOwner.OfValue("m.a", "g"), 0)));
        assertEquals("check.apply.notfunction",
                assertInstanceOf(CompileException.class, e).diagnostic().messageKey());
    }

    /**
     * A name the language itself gives, applied. `Some` and `None` are told apart earlier (E1303),
     * so what reaches here is a rounding mode — a bare identifier the operation taking one reads
     * rather than evaluates. An author can write it, so they are told, not shown a compiler bug.
     */
    @Test
    void aBuiltinIsToldItIsNotAFunction() {
        RuntimeException e = answerFor(new ValueName.Builtin("HALF_UP"));
        CompileException c = assertInstanceOf(CompileException.class, e);
        assertEquals("check.builtin.notfunction", c.diagnostic().messageKey());
        assertEquals(List.of("HALF_UP"), List.of(c.diagnostic().args()));
    }

    /**
     * The rest name a call that should have been expanded, substituted or rewritten before the check
     * ran. That is the compiler disagreeing with itself, so it is raised as one — an author cannot
     * act on it, and dressing it as a language error would have them try.
     */
    @Test
    void anUnexpandedCallIsAnInternalError() {
        for (ValueName denotes : List.of(
                new ValueName.Helper("m", "f"),
                new ValueName.Stdlib("List.map"),
                new ValueName.Unresolved("f"))) {
            RuntimeException e = answerFor(denotes);
            assertInstanceOf(IllegalStateException.class, e, denotes.toString());
            assertTrue(e.getMessage().contains("7:3"), () -> "says where: " + e.getMessage());
        }
    }

    @Test
    void anUnresolvedCallIsAnInternalError() {
        assertInstanceOf(IllegalStateException.class, answerFor(null));
    }
}
