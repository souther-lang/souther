package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * The abstract base of an injected behavior is public whatever {@code exposing} says (spec 13.3),
 * because a behavior subject to injection is implemented outside its module. The implementation
 * overrides {@code apply}, so it writes the input type and the output type; a type the module keeps
 * to itself cannot be written there, and no raw-typed override stands in for it — javac reports the
 * erased clash. So an injected behavior's input and output are exposed by the module that declares
 * them, whether or not the behavior itself is in {@code exposing}.
 */
class CompileInjectionSignatureExposureTest {

    @Test
    void theInputTypeOfAnInjectedBehaviorIsExposed() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                exposing ( Member )

                data Id = String
                data Member = { id: Id }

                behavior findMember : (id: Id) -> Member
                """));

        assertTrue(e.getMessage().contains("Id"), e.getMessage());
        assertTrue(e.getMessage().contains("findMember"), e.getMessage());
    }

    @Test
    void theOutputTypeOfAnInjectedBehaviorIsExposed() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                exposing ( Id )

                data Id = String
                data Member = { id: Id }

                behavior findMember : (id: Id) -> Member
                """));

        assertTrue(e.getMessage().contains("Member"), e.getMessage());
        assertTrue(e.getMessage().contains("findMember"), e.getMessage());
    }

    @Test
    void aTypeCarriedInsideACollectionIsReachedToo() {
        // `List<Id>` puts `Id` in `apply`'s signature as surely as a bare `Id` does.
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                exposing ( Member )

                data Id = String
                data Member = { id: Id }

                behavior findAll : (ids: List<Id>) -> Member
                """));

        assertTrue(e.getMessage().contains("Id"), e.getMessage());
    }

    @Test
    void aUnitCaseOfTheOutputStillNeedsNoExposure() {
        // The output is the generated union, which is public whatever exposing says, and the unit
        // case is reached through the protected factory without being named — so the rule does not
        // reach it and E1305's exemption stands.
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo
                exposing ( Id, Member )

                data Id = String
                data Member = { id: Id }
                data 会員なし

                behavior findMember : (id: Id) -> Member | 会員なし
                    constructs 会員なし
                """));
    }
}
