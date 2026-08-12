package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A field taken off a value a row can already build. A spread copies every field of such a value and
 * was admitted; reading one of them back was not, so a fixture for a collection derived from another
 * value had to be written out again as a literal.
 *
 * <p>What a taken field supplies is its declaration's to say — which is the answer a value cannot
 * give where the field holds an empty collection, there being no element to name. Where the value is
 * one a helper answered with, the answer says it, as it does wherever a helper stands.
 */
class CompileFixtureProjectsAFieldTest {

    @Test
    void anExpectedValueReadsAFieldOffANamedValue() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data Line = { done: Bool }
                data Ticket = { lines: List<Line> }

                let sample = Ticket { lines = [ Line { done = false } ] }

                behavior linesOf : (t: Ticket) -> List<Line>
                let linesOf (t) = t.lines

                example linesOf
                    | "an expected value reads a field" : (sample) -> sample.lines
                """));
    }
}
