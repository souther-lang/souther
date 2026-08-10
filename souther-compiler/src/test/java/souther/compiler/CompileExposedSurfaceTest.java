package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a module reaches out with may not rest on what it keeps to itself. An exposed data's field
 * types, an exposed behavior's input and output, and an injected behavior's input and output —
 * whose abstract base is public whatever {@code exposing} says — are exposed by the module that
 * declares them. Otherwise a reader holds a value it has no name for and cannot use, and the
 * generated classes carry a public surface over classes it may not touch (issue #187).
 *
 * <p>Reported where the module decides it, as Rust's {@code private_interfaces} and F#'s
 * {@code FS0410} do, rather than at each reader that runs into it.
 */
class CompileExposedSurfaceTest {

    private static CompileException refused(String source) {
        return assertThrows(CompileException.class, () -> Compiler.compile(source));
    }

    @Test
    void anExposedDataMayNotRestOnATypeTheModuleKeepsToItself() {
        CompileException e = refused("""
                module demo exposing ( Order )

                data UserId = String
                data Order = { by: UserId }
                """);

        assertTrue(e.getMessage().contains("UserId"), e.getMessage());
        assertTrue(e.getMessage().contains("Order"), e.getMessage());
    }

    @Test
    void aTypeCarriedInsideACollectionIsReachedToo() {
        CompileException e = refused("""
                module demo exposing ( Order )

                data UserId = String
                data Order = { by: List<UserId> }
                """);

        assertTrue(e.getMessage().contains("UserId"), e.getMessage());
    }

    @Test
    void anExposedBehaviorMayNotTakeOne() {
        CompileException e = refused("""
                module demo exposing ( Out, run )

                data UserId = String
                data Out = { s: String }

                behavior run : (id: UserId) -> Out
                    constructs Out
                let run (id) = Out { s = "k" }
                """);

        assertTrue(e.getMessage().contains("UserId"), e.getMessage());
        assertTrue(e.getMessage().contains("run"), e.getMessage());
    }

    @Test
    void anExposedBehaviorMayNotAnswerWithOne() {
        CompileException e = refused("""
                module demo exposing ( Id, run )

                data Id = String
                data Out = { s: String }

                behavior run : (id: Id) -> Out
                    constructs Out
                let run (id) = Out { s = "k" }
                """);

        assertTrue(e.getMessage().contains("Out"), e.getMessage());
        assertTrue(e.getMessage().contains("run"), e.getMessage());
    }

    @Test
    void anInjectionTargetIsReachedEvenWhereItIsNotExposed() {
        // Its abstract base is public whatever `exposing` says, and the Java implementation writes
        // the input type where it overrides `apply` (spec §java-base-class).
        CompileException e = refused("""
                module demo exposing ( Member )

                data Id = String
                data Member = { name: String }

                behavior findMember : (id: Id) -> Member
                """);

        assertTrue(e.getMessage().contains("Id"), e.getMessage());
        assertTrue(e.getMessage().contains("findMember"), e.getMessage());
    }

    @Test
    void whatTheModuleKeepsToItselfMayRestOnWhatItKeepsToItself() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo exposing ( Out )

                data UserId = String
                data Internal = { by: UserId }
                data Out = { s: String }
                """));
    }

    @Test
    void anExposedSumMayStillKeepItsCasesToItself() {
        // A case reaches a reader through the decoder and, for an injected output, through the
        // generated factory — without being named. That is E1305's allowance and it stands.
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo exposing ( Contact )

                data EmailC = { email: String }
                data PhoneC = { phone: String }
                data Contact = EmailC | PhoneC
                """));
    }
}
