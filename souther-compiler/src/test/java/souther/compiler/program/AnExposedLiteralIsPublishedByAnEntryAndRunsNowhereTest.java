package souther.compiler.program;

import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A value that folds to a literal is declared and, when the module lists it, published through an
 * entry. It has no place to run (ADR-0074), so the module builds no {@link CheckedValue} for it.
 */
class AnExposedLiteralIsPublishedByAnEntryAndRunsNowhereTest {

    private static final ValueName.Helper IT = new ValueName.Helper("m", "it");

    @Test
    void anIntLiteral() {
        isPublishedByAnEntryAndRunsNowhere("3");
    }

    @Test
    void aDecimalLiteral() {
        isPublishedByAnEntryAndRunsNowhere("1.50m");
    }

    @Test
    void aStringLiteral() {
        isPublishedByAnEntryAndRunsNowhere("\"three\"");
    }

    @Test
    void aBoolLiteral() {
        isPublishedByAnEntryAndRunsNowhere("true");
    }

    @Test
    void aKeptLiteralIsDeclaredAndHasNoEntry() {
        CheckedModule compiled = CheckedProgram.of(List.of("""
                module m exposing ( other )

                let it = 3

                let other = [1, 2]
                """)).module("m");

        assertEquals(Publication.KEPT, compiled.publicationOfValue(IT));
        assertThrows(IllegalArgumentException.class, () -> compiled.valueEntry(IT));
        assertThrows(IllegalArgumentException.class, () -> compiled.value(IT));
    }

    @Test
    void aComputedValueBesideItStillRunsAsAValue() {
        CheckedModule compiled = CheckedProgram.of(List.of("""
                module m exposing ( it, other )

                let it = 3

                let other = [1, 2]
                """)).module("m");

        ValueName.Helper other = new ValueName.Helper("m", "other");
        assertEquals(Publication.PUBLISHED, compiled.publicationOfValue(other));
        assertEquals(other, compiled.valueEntry(other).value());
        assertEquals(other, compiled.value(other).name());
        assertTrue(compiled.values().stream().noneMatch(each -> each.name().equals(IT)));
    }

    private static void isPublishedByAnEntryAndRunsNowhere(String literal) {
        CheckedModule compiled = CheckedProgram.of(List.of("""
                module m exposing ( it )

                let it = %s
                """.formatted(literal))).module("m");

        assertEquals(Publication.PUBLISHED, compiled.publicationOfValue(IT), literal);
        assertEquals(IT, compiled.valueEntry(IT).value(), literal);
        assertTrue(compiled.values().isEmpty(), literal);
        assertThrows(IllegalArgumentException.class, () -> compiled.value(IT), literal);
    }
}
