package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A case of a sum and a member of an output union both travel under the discriminator {@code "type"}
 * (spec 11.2, 19.8), which is written beside the fields the case lays flatly. A case declaring a
 * field of that name would have its own value written over by the tag, so it is refused where it is
 * declared rather than lost where it is encoded.
 */
class CompileDiscriminatorFieldTest {

    @Test
    void aSumCaseCarryingTheDiscriminatorAsAFieldIsRejected() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module m exposing ( Ok, Miss, Answer )
                data Ok = { type: String }
                data Miss = { reason: String }
                data Answer = Ok | Miss
                """));
        assertTrue(e.getMessage().contains("type"), e.getMessage());
        assertTrue(e.getMessage().contains("Ok"), e.getMessage());
    }

    @Test
    void aUnionMemberCarryingTheDiscriminatorAsAFieldIsRejected() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module m exposing ( Ok, NotFound, bill )
                data Ok = { type: String }
                data NotFound
                behavior bill : (n: Int) -> Ok | NotFound constructs Ok, NotFound
                let bill (n) = if n > 0 then Ok { type = "mine" } else NotFound
                """));
        assertTrue(e.getMessage().contains("type"), e.getMessage());
        assertTrue(e.getMessage().contains("Ok"), e.getMessage());
    }

    @Test
    void aNestedSumsLeafIsSubjectToItThroughTheUnionItReaches() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module m exposing ( Hit, Miss, Answer, NoAnswer, ask )
                data Hit = { type: String }
                data Miss = { reason: String }
                data Answer = Hit | Miss
                data NoAnswer
                behavior ask : (n: Int) -> Answer | NoAnswer constructs Hit, Miss, NoAnswer
                let ask (n) = {
                    guard n >= 0 else NoAnswer
                    if n > 0 then Hit { type = "mine" } else Miss { reason = "no" }
                }
                """));
        assertTrue(e.getMessage().contains("Hit"), e.getMessage());
    }

    @Test
    void aFieldNamedTypeOnADataThatIsNeitherCompiles() {
        // The name is only taken where the discriminator is written: a data that is no case and no
        // union member never sits beside one.
        assertTrue(Compiler.compile("""
                module m exposing ( Account, describe )
                data Account = { type: String }
                behavior describe : (a: Account) -> String
                let describe (a) = a.type
                """).containsKey("m.Account"));
    }
}
