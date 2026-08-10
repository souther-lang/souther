package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.msg.HelperMessage;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A message names a type the way the author can write it. `+?+` marks where an optional is made and
 * is written on a whole type only, so an optional standing in a type argument or a tuple's member is
 * named {@code Option<T>} — {@code List<T?>} is written nowhere
 * (spec {@code [#an-optional-is-not-written-inside-another-type]}). A function type's parameter and
 * its result are whole types, so an optional there keeps the mark.
 */
class ATypeInsideAnotherTypeIsNamedTheWayItIsWrittenTest {

    private static Diagnostic diagnosticOf(String src) {
        return assertThrows(CompileException.class, () -> Compiler.compile(src)).diagnostic();
    }

    private static String gotFrom(String helper) {
        Diagnostic d = diagnosticOf("module demo\ndata R = { n: Int }\n" + helper + "\n");
        return assertInstanceOf(HelperMessage.TheBodyIsNotWhatTheHelperDeclares.class, d.said()).body();
    }

    @Test
    void anOptionalInATypeArgumentIsNamedByItsType() {
        assertEquals("List<Option<Int>>", gotFrom("let f (xs: List<Option<Int>>) : Int = xs"));
    }

    @Test
    void anOptionalInsideTwoTypeArgumentsIsNamedAtEachLevel() {
        assertEquals("Map<String, List<Option<Int>>>",
                gotFrom("let f (xs: Map<String, List<Option<Int>>>) : Int = xs"));
    }

    // A whole type keeps the mark: this is the field spelling, and it is what the author wrote.
    @Test
    void anOptionalStandingAsAWholeTypeKeepsTheMark() {
        assertEquals("Int?", gotFrom("let f (v: Option<Int>) : String = v"));
    }
}
