package souther.compiler.program;

import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * {@link CheckedModule}'s invariant over {@link CheckedValueEntry} holds in both directions: a
 * published value has one, and a value with one is published.
 *
 * <p>The constructor already refused the first direction — a published value the assembler forgot
 * to mint an entry for. Nothing refused the second: a {@code CheckedModule} built with an entry for
 * a value it keeps was accepted, which is the same upstream/downstream disagreement ADR-0074 exists
 * to make impossible to construct at all, one arm of it left open.
 */
class AValueEntryBelongsToExactlyThePublishedValuesTest {

    private static final String MODULE = """
            module m exposing ( ys )

            let ks = [1, 2, 3]

            let ys = List.reverse(ks)
            """;

    @Test
    void aKeptValueGivenAnEntryIsRefused() {
        CheckedModule compiled = CheckedProgram.of(List.of(MODULE)).module("m");
        CheckedValue kept = compiled.value(new ValueName.Helper("m", "ks"));
        CheckedValueEntry entryForYs = compiled.valueEntry(new ValueName.Helper("m", "ys"));
        // Reuses a real, typed body rather than fabricating one: this test is about the pairing
        // between a value and an entry, not about what either's `Core` holds.
        CheckedValueEntry entryForKept = new CheckedValueEntry(kept.name(), entryForYs.body());

        assertThrows(IllegalStateException.class, () -> new CheckedModule("m", List.of(), List.of(),
                List.of(kept), List.of(entryForKept), List.of(), Set.of()));
    }
}
