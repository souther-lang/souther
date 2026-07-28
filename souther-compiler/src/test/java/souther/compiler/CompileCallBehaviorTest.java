package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A behavior whose requirement set is empty is called from a body by name, in the module that
 * declares it and in one that imports it (spec {@code [#calling-a-behavior]}, ADR-0068).
 *
 * <p>What a body could call used to depend on which side of a module boundary the callee was on: a
 * behavior of this module was refused outright, and an imported one was reported as an arbitrary JVM
 * call. Both meant a pure rule shared between two modules had to be copied, or written twice — once
 * as the behavior the specification names and once as a helper twin that could actually be called.
 */
class CompileCallBehaviorTest {

    private static final String UP = """
            module up exposing ( A, B, rateOf )

            data A = { n: Int }
            data B = { m: Int }

            behavior rateOf : (a: A) -> B
                constructs B
            let rateOf (a) = B { m = a.n * 2 }
            """;

    @Test
    void aBehaviorOfThisModuleIsCalledByName() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module same exposing ( A, B, Out, a2b, use )

                data A = { n: Int }
                data B = { m: Int }
                data Out = { o: Int }

                behavior a2b : (a: A) -> B
                    constructs B
                let a2b (a) = B { m = a.n * 2 }

                behavior use : (a: A) -> Out
                    constructs Out
                let use (a) = Out { o = a2b(a).m }
                """));
    }

    @Test
    void anImportedBehaviorIsCalledTheSameWay() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of(UP, """
                module down exposing ( Out, use )

                import up ( A, B, rateOf )

                data Out = { o: Int }

                behavior use : (a: A) -> Out
                    constructs Out
                let use (a) = Out { o = rateOf(a).m }
                """)));
    }

    /**
     * The call yields the callee's declared output, so a caller that does not handle a case has to
     * declare it. Nothing departs on its own — that is what {@code >->} does, and a call is not a
     * stage.
     */
    @Test
    void aCallYieldsTheWholeDeclaredOutputAndIsOpenedWithMatch() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module route exposing ( In, Ok, Refused, Out, classify, use )

                data In = { n: Int }
                data Ok = { n: Int }
                data Refused = { why: String }
                data Out = { o: Int }

                behavior classify : (i: In) -> Ok | Refused
                    constructs Ok, Refused
                let classify (i) =
                    if i.n > 0 then Ok { n = i.n } else Refused { why = "not positive" }

                behavior use : (i: In) -> Out | Refused
                    constructs Out
                let use (i) = match classify(i) with
                    | Ok o -> Out { o = o.n }
                    | Refused r -> r
                """));
    }

    /** A behavior that requires something is reached through `requires`, not by name. */
    @Test
    void aBehaviorThatRequiresSomethingIsNotCallableByName() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module dep exposing ( In, Out, Stamp, now, stamp, use )

                data In = { n: Int }
                data Out = { o: Int }
                data Stamp = { at: String }

                behavior now : (i: In) -> Stamp

                behavior stamp : (i: In) -> Out
                    requires now
                    constructs Out
                let stamp (i, now) = Out { o = i.n }

                behavior use : (i: In) -> Out
                    constructs Out
                let use (i) = stamp(i)
                """));
        assertTrue(e.getMessage().contains("stamp"), e.getMessage());
    }

    /**
     * A behavior with a `let` of its own may be a requirement, so a rule written in Souther is
     * shared the same way one implemented in Java is. Two unrelated modules depend on the same one.
     */
    @Test
    void anImplementedBehaviorWithRequiresIsNamedInRequiresAndCalled() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of("""
                module user exposing ( Id, Row, Person, Missing, load, fetch )

                data Id = String
                data Row = { id: Id, name: String, active: Bool }
                data Person = { id: Id, name: String }
                data Missing = { id: Id }

                behavior load : (id: Id) -> Row | Missing
                    constructs Row, Missing

                behavior fetch : (id: Id) -> Person | Missing
                    requires load
                    constructs Person, Missing
                let fetch (id, load) = match load(id) with
                    | Row r -> if r.active then Person { id = r.id, name = r.name }
                               else Missing { id = id }
                    | Missing m -> m
                """, """
                module orders exposing ( Order, Placed, Unknown, place )

                import user ( Id, Person, Missing, fetch )

                data Order = { by: Id }
                data Placed = { by: Id, name: String }
                data Unknown = { by: Id }

                behavior place : (o: Order) -> Placed | Unknown
                    requires fetch
                    constructs Placed, Unknown
                let place (o, fetch) = match fetch(o.by) with
                    | Person p -> Placed { by = p.id, name = p.name }
                    | Missing m -> Unknown { by = o.by }
                """, """
                module billing exposing ( Invoice, Issued, NoSuch, issue )

                import user ( Id, Person, Missing, fetch )

                data Invoice = { to: Id }
                data Issued = { to: Id, name: String }
                data NoSuch = { to: Id }

                behavior issue : (i: Invoice) -> Issued | NoSuch
                    requires fetch
                    constructs Issued, NoSuch
                let issue (i, fetch) = match fetch(i.to) with
                    | Person p -> Issued { to = p.id, name = p.name }
                    | Missing m -> NoSuch { to = i.to }
                """)));
    }

    /** A behavior does not recurse, whether the loop is calls or `requires` (E1608). */
    @Test
    void aBehaviorThatReachesItselfThroughCallsIsRejected() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module loop exposing ( A, R, there, back )

                data A = { x: Int }
                data R = { z: Int }

                behavior there : (a: A) -> R
                let there (a) = back(a)

                behavior back : (a: A) -> R
                let back (a) = there(a)
                """));
        assertEquals("E1608", e.code(), e.getMessage());
        assertTrue(e.getMessage().contains("there -> back -> there")
                || e.getMessage().contains("back -> there -> back"), e.getMessage());
    }

    @Test
    void aRequiresCycleIsRejected() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module loop exposing ( A, R, p, q )

                data A = { x: Int }
                data R = { z: Int }

                behavior p : (a: A) -> R
                    requires q
                let p (a, q) = q(a)

                behavior q : (a: A) -> R
                    requires p
                let q (a, p) = p(a)
                """));
        assertEquals("E1608", e.code(), e.getMessage());
    }

    /**
     * Run rather than merely compiled. An {@code example} is evaluated during the compile and a row
     * that does not hold is a compile error, so this passing is the emitted call working — a
     * cross-module call that compiles is not evidence that it links.
     */
    @Test
    void theCalledBehaviorActuallyRuns() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module run exposing ( A, Out, a2b, B, use )

                data A = { n: Int }
                data B = { m: Int }
                data Out = { o: Int }

                behavior a2b : (a: A) -> B
                    constructs B
                let a2b (a) = B { m = a.n * 2 }

                behavior use : (a: A) -> Out
                    constructs Out
                let use (a) = Out { o = a2b(a).m }

                example use
                    | "the called behavior runs" : (A { n = 21 }) -> Out { o = 42 }
                """));
    }
}
