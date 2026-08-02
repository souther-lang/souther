package souther.compiler;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;

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
}
