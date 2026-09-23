package souther.program.api;

import souther.compiler.program.CheckedHelper;
import souther.compiler.program.CheckedModule;
import souther.compiler.program.CheckedProgram;
import souther.compiler.program.CheckedValueEntry;
import souther.compiler.program.Publication;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether a module publishes a value, and the entry it holds for one it does — the two answers
 * issue #1885 asked for once {@link CheckedHelper} stopped standing in for both a value's entry and
 * a row's harness value.
 */
class AnOutputReadsThePublicationOfAValueTest {

    private static final String MODULE = """
            module m exposing ( ys )

            let ks = [1, 2, 3]

            let ys = List.reverse(ks)
            """;

    @Test
    void aValueTheClauseListsIsPublishedAndOneItDoesNotIsKept() {
        CheckedModule module = CheckedProgram.of(List.of(MODULE)).module("m");

        assertEquals(Publication.PUBLISHED,
                module.publicationOfValue(new ValueName.Helper("m", "ys")));
        assertEquals(Publication.KEPT, module.publicationOfValue(new ValueName.Helper("m", "ks")));
    }

    @Test
    void aValueThisModuleDoesNotBuildIsRefusedRatherThanKept() {
        CheckedModule module = CheckedProgram.of(List.of(MODULE)).module("m");

        assertThrows(IllegalArgumentException.class, () -> module.publicationOfValue(
                new ValueName.Helper("m", "nobodyWroteThis")));
        assertThrows(IllegalArgumentException.class, () -> module.publicationOfValue(
                new ValueName.Helper("somewhere.else", "ys")));
    }

    /** A published value's entry is the nullary bridge to it, and its own kind of thing — not one
     *  of the module's carried helpers. */
    @Test
    void aPublishedValueHasAnEntryAndItIsNotAHelper() {
        CheckedModule module = CheckedProgram.of(List.of(MODULE)).module("m");
        ValueName.Helper ys = new ValueName.Helper("m", "ys");

        CheckedValueEntry entry = module.valueEntry(ys);

        assertEquals(ys, entry.value());
        assertEquals(List.of(entry), module.valueEntries());
        for (CheckedHelper helper : module.helpers()) {
            assertFalse(helper.declares().equals(ys), helper + " is carried as a helper too");
        }
    }

    /** A value this module keeps has no entry: only publication mints one (ADR-0074). */
    @Test
    void aKeptValueHasNoEntry() {
        CheckedModule module = CheckedProgram.of(List.of(MODULE)).module("m");

        assertThrows(IllegalArgumentException.class,
                () -> module.valueEntry(new ValueName.Helper("m", "ks")));
        assertTrue(module.valueEntries().stream()
                .noneMatch(entry -> entry.value().name().equals("ks")));
    }
}
