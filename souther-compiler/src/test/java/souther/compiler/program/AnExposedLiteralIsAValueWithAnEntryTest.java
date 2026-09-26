package souther.compiler.program;

import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A module that exposes a value whose body is a literal becomes a checked program, with the value
 * built and its entry beside it, for each kind of literal the language has.
 */
class AnExposedLiteralIsAValueWithAnEntryTest {

    @Test
    void anIntLiteral() {
        holdsTheValueAndItsEntry("3");
    }

    @Test
    void aDecimalLiteral() {
        holdsTheValueAndItsEntry("1.50m");
    }

    @Test
    void aStringLiteral() {
        holdsTheValueAndItsEntry("\"three\"");
    }

    @Test
    void aBoolLiteral() {
        holdsTheValueAndItsEntry("true");
    }

    private static void holdsTheValueAndItsEntry(String literal) {
        String source = """
                module m exposing ( it )

                let it = %s
                """.formatted(literal);

        CheckedModule compiled = CheckedProgram.of(List.of(source)).module("m");

        ValueName.Helper it = new ValueName.Helper("m", "it");
        assertNotNull(compiled.value(it), literal);
        assertEquals(it, compiled.valueEntry(it).value(), literal);
    }
}
