package souther.compiler;

import org.junit.jupiter.api.Test;

import java.util.List;

import souther.compiler.diag.CompileException;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A fixture reads a bare name as what it denotes, so what a row builds does not depend on how the
 * bindings around it are spelled.
 *
 * <p>A fixture's names used to be worked out again where the row was built — `None`, then a unit
 * data of that spelling, then a binding in force, then a value the module defines — so a binding
 * spelled like a unit data was read as that unit and the row built the wrong value.
 */
class ExampleFixtureShadowingTest {

    private static final String MODULE = """
            module demo
            data Empty
            data Box = { n: Int }
            data Out = { n: Int }

            let fixture = {
                let NAME = Box { n = 1 }
                NAME
            }

            behavior go : (b: Box) -> Out constructs Out
            let go (b) = Out { n = b.n }

            example go
                | "one" : (fixture) -> Out { n = 1 }
            """;

    @Test
    void aFixtureBindingSpelledLikeAUnitDataIsStillTheBinding() {
        for (String spelled : List.of("held", "Empty")) {
            assertDoesNotThrow(() -> Compiler.compile(MODULE.replace("NAME", spelled)),
                    "the fixture holds a Box, with a binding spelled " + spelled);
        }
    }

    /** And a binding spelled like a value the module defines is the binding, not that value. */
    @Test
    void aFixtureBindingSpelledLikeAValueIsStillTheBinding() {
        String source = """
                module demo
                data Box = { n: Int }
                data Out = { n: Int }

                let other = Box { n = 9 }

                let fixture = {
                    let NAME = Box { n = 1 }
                    NAME
                }

                behavior go : (b: Box) -> Out constructs Out
                let go (b) = Out { n = b.n }

                example go
                    | "one" : (fixture) -> Out { n = 1 }
                """;
        for (String spelled : List.of("held", "other")) {
            assertDoesNotThrow(() -> Compiler.compile(source.replace("NAME", spelled)),
                    "the fixture holds `Box { n = 1 }`, with a binding spelled " + spelled);
        }
    }

    /**
     * Two bindings of one spelling, one holding the other. Not a value reaching itself — the second
     * reads the first, which is closed by the time the second is open — so it is not refused as one.
     */
    @Test
    void twoBindingsOfOneSpellingAreNotAValueReachingItself() {
        String source = """
                module demo
                data Box = { n: Int }
                data Out = { n: Int }

                let fixture = {
                    let x = Box { n = 1 }
                    let NAME = x
                    NAME
                }

                behavior go : (b: Box) -> Out constructs Out
                let go (b) = Out { n = b.n }

                example go
                    | "one" : (fixture) -> Out { n = 1 }
                """;
        for (String spelled : List.of("y", "x")) {
            assertDoesNotThrow(() -> Compiler.compile(source.replace("NAME", spelled)),
                    "the inner binding reads the outer one, spelled " + spelled);
        }
    }

    /** A value that does reach itself is still refused, and named. */
    @Test
    void aValueDefinedInTermsOfItselfIsStillRefused() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                data Box = { n: Int }
                data Out = { n: Int }

                let fixture = other
                let other = fixture

                behavior go : (b: Box) -> Out constructs Out
                let go (b) = Out { n = b.n }

                example go
                    | "one" : (fixture) -> Out { n = 1 }
                """));
        assertTrue(e.getMessage().contains("itself"), e.getMessage());
    }
}
