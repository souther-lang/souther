package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.CompileException;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a row operand is held to comes from what the behavior is, and reaches only what the row can
 * reach.
 *
 * <p>Three readings had answers of their own here, and each of them was a way for a row to state
 * something the language would have refused anywhere else it was written.
 *
 * <ul>
 *   <li>Where a value stands was read off the {@code behavior} forms this module wrote, so a
 *       composition — which has no parameter list — contributed nothing, and what a row wrote at
 *       one was compiled against no type at all. It reached the JVM as a cast.</li>
 *   <li>A bare type name was left uncompiled wherever it stood, so a value the model is given was
 *       still built by the reading this change removes.</li>
 *   <li>The definition a row's operand is compiled as was handed the behaviors a body may call,
 *       and a row is not inside a body: nothing injects a dependency into it.</li>
 * </ul>
 */
class ARowOperandIsHeldToWhatItsPositionIsTest {

    private static CompileException refused(String source) {
        return assertThrows(CompileException.class, () -> Compiler.compile(source),
                "the row states what the position does not take");
    }

    /** A composition takes what its first stage takes, and a row is held to it. */
    @Test
    void aCompositionSaysWhatItsRowsStandAt() {
        String model = """
                module demo

                data AmountN = Int
                data In  = { a: AmountN }
                data Mid = { b: AmountN }
                data Out = { c: AmountN }

                behavior first : (i: In) -> Mid
                    constructs Mid
                let first (i) = Mid { b = i.a }

                behavior second : (m: Mid) -> Out
                    constructs Out
                let second (m) = Out { c = m.b }

                behavior whole = first >-> second
                """;
        Compiler.compile(model + """

                example whole
                    | "holds" : (In { a = AmountN(1) }) -> Out { c = AmountN(1) }
                """);
        // Read off the signature the pipeline settles, which is where a composition's shape is
        // worked out. Read off the `behavior` forms instead, this position said nothing and the
        // value reached the behavior as a cast the JVM refused.
        CompileException e = refused(model + """

                example whole
                    | "the wrong type" : (Mid { b = AmountN(1) }) -> Out { c = AmountN(1) }
                """);
        assertEquals("E1812", e.diagnostic().code(), e.getMessage());
        assertTrue(e.getMessage().contains("In") && e.getMessage().contains("Mid"),
                e.getMessage());
    }

    /** A bare type name at a supplied position is a value, and is compiled as one. */
    @Test
    void aSuppliedBareNameIsCompiledLikeAnyOtherValue() {
        String model = """
                module demo

                data Found = { id: String }
                data Missing = { why: String }
                data Done

                behavior lookup : () -> Found | Missing

                behavior use : () -> Done
                    depends on lookup
                let use (lookup) = match lookup() with
                    | Found   -> Done
                    | Missing -> Done
                """;
        // A record's name stands for no value, and the row is told so where it is written rather
        // than being answered by a reading of its own.
        CompileException e = refused(model + """

                example use
                    | "a record's name" : () with lookup = Missing -> Done
                """);
        assertEquals("E1023", e.diagnostic().code(), e.getMessage());
        assertTrue(e.getMessage().contains("Missing"), e.getMessage());
    }

    /** A unit case's name is a value, so the same rule admits it. */
    @Test
    void aUnitCaseIsStillAValueThere() {
        Compiler.compile("""
                module demo

                data Yes
                data No
                data Flag = Yes | No
                data Ok = { n: Int }

                behavior take : (flag: Flag) -> Ok
                    constructs Ok
                let take (flag) = Ok { n = 1 }

                example take
                    | "a unit case" : (Yes) -> Ok { n = 1 }
                """);
    }

    /**
     * A row may not call what the behavior it is about depends on.
     *
     * <p>A row supplies the values a behavior is applied to and stands in for what that behavior
     * depends on. It is not inside the application, so the dependencies are not in force where it
     * is computed — and the definition it is compiled as is nullary and static, with nothing
     * injected into it.
     */
    @Test
    void aRowMayNotCallWhatTheBehaviorDependsOn() {
        String model = """
                module demo

                data Id = String
                data Found = { id: Id }
                data Ok = { n: Int }

                behavior lookup : (id: Id) -> Found

                behavior use : (id: Id) -> Ok
                    depends on lookup
                    constructs Ok
                let use (id, lookup) = Ok { n = String.length(lookup(id).id.value) }

                fake lookup
                    | (Id("a")) -> Found { id = Id("a") }
                """;
        CompileException e = refused(model + """

                example use
                    | "calls the dependency" : (lookup(Id("a")).id) -> Ok { n = 1 }
                """);
        assertEquals("E1818", e.diagnostic().code(), e.getMessage());
        assertTrue(e.getMessage().contains("lookup"), e.getMessage());
    }

    /** And not through a helper either: what a helper reaches is what the row reaches. */
    @Test
    void norThroughAHelperThatReachesIt() {
        CompileException e = refused("""
                module demo

                data Id = String
                data Found = { id: Id }
                data Ok = { n: Int }

                behavior lookup : (id: Id) -> Found

                behavior use : (id: Id) -> Ok
                    depends on lookup
                    constructs Ok
                let use (id, lookup) = Ok { n = String.length(lookup(id).id.value) }

                let through (id: Id): Id = lookup(id).id

                fake lookup
                    | (Id("a")) -> Found { id = Id("a") }

                example use
                    | "through a helper" : (through(Id("a"))) -> Ok { n = 1 }
                """);
        assertEquals("E1818", e.diagnostic().code(), e.getMessage());
    }
}
