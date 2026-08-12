package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;
import souther.compiler.diag.CompileException;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two modules may each declare a {@code Mid}, and a message that shows one against the other has to
 * tell them apart: {@code Mid} against {@code Mid} says nothing. A name is written with its module
 * only where the other side of the same message uses that name for a different type.
 */
class CompileAmbiguousTypeNameTest {

    private static final String UP = """
            module up exposing ( In, Mid, twice )
            data In = { n: Int }
            data Mid = { n: Int }
            behavior twice : (i: In) -> Mid constructs Mid
            let twice (i) = Mid { n = i.n * 2 }
            """;

    private static final String OTHER = """
            module other exposing ( In, Mid, twice )
            data In = { n: Int }
            data Mid = { n: Int }
            behavior twice : (i: In) -> Mid constructs Mid
            let twice (i) = Mid { n = i.n * 3 }
            """;

    @Test
    void aMismatchBetweenTwoSameNamedTypesNamesTheirModules() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(UP, OTHER, """
                        module d exposing ( Out, flow : Out )
                        data Out = { n: Int }
                        behavior plus : (m: up.Mid) -> Out constructs Out
                        let plus (m) = Out { n = m.n + 1 }
                        behavior flow = other.twice >-> plus
                        """)));

        assertEquals("other.Mid", e.diagnostic().diff().actualType(), e.getMessage());
        assertEquals("up.Mid", e.diagnostic().diff().expectedType(), e.getMessage());
    }

    @Test
    void namesThatAreNotAmbiguousStayBare() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(UP, """
                        module d exposing ( Out, flow : Out )
                        data Out = { n: Int }
                        data Other = { s: String }
                        behavior plus : (m: Other) -> Out constructs Out
                        let plus (m) = Out { n = 1 }
                        behavior flow = up.twice >-> plus
                        """)));

        assertEquals("Mid", e.diagnostic().diff().actualType(), e.getMessage());
        assertEquals("Other", e.diagnostic().diff().expectedType(), e.getMessage());
    }

    /** The rendering reaches inside a collection, and only the colliding name is written out. */
    @Test
    void onlyTheCollidingNameIsQualified() {
        Type listOfUpMid = Type.list(Type.ref(new TypeName("up", "Mid")));
        Type listOfOtherMid = Type.list(Type.ref(new TypeName("other", "Mid")));
        Type listOfOut = Type.list(Type.ref(new TypeName("d", "Out")));

        assertEquals("List<up.Mid>", Type.show(listOfUpMid, listOfOtherMid));
        assertEquals("List<Mid>", Type.show(listOfUpMid, listOfOut));
        assertTrue(Type.show(listOfUpMid).equals("List<Mid>"), "the one-type rendering is unchanged");
    }
}
