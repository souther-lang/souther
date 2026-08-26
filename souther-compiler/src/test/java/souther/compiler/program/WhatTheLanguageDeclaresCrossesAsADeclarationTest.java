package souther.compiler.program;

import souther.compiler.DefaultStdlib;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * The declarations the language gives cross whole, and an address is one world's or the other's.
 *
 * <p>In this compiler's own tests because it is the two sides that are held together here: what the
 * library declares, which is {@code stdlib}'s answer, and what the snapshot carries. An output
 * outside cannot see the first, so a test written there could only say the snapshot agreed with
 * itself.
 */
class WhatTheLanguageDeclaresCrossesAsADeclarationTest {

    private static final String MODULE = """
            module demo

            behavior rounded : (d: Decimal) -> Decimal

            let rounded (d) = Decimal.round(2, HALF_UP, d)
            """;

    /**
     * Every declaration the library gives is in the snapshot, and the snapshot invents none.
     *
     * <p>What this holds is that nothing selects on the way over. The snapshot is one reading of the
     * library's own declarations, and a reading that took some of them would leave an output holding
     * values of the rest with nothing to lay them out by — which is the shape of what this change
     * was about, one selection later.
     */
    @Test
    void everyDeclarationTheLibraryGivesIsInTheSnapshotAndNoOther() {
        List<TypeSymbol.AtModule> carried =
                CheckedProgram.of(List.of(MODULE)).languageDeclarations().stream()
                        .map(CheckedData::name).sorted().toList();

        assertEquals(DefaultStdlib.get().languageDeclarations().keySet().stream()
                        .map(TypeSymbols::declared).sorted().toList(),
                carried);
    }

    /**
     * One address is declared by the language or by a module, and never by both.
     *
     * <p>Nothing of a compilation is in the reserved namespace, so the two never meet — and were
     * they to, whichever was filed second would silently be the answer every reader got. Refused
     * where the index is built, which is the one place both are in hand.
     */
    @Test
    void oneAddressIsNotDeclaredByBothWorlds() {
        CheckedData twice = new CheckedData.Unit(named("demo", "Mode"));

        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> new CheckedProgram(List.of(module("demo", twice)), List.of(twice), Set.of()));

        assertEquals("`demo.Mode` is declared by the language and by a module", refused.getMessage());
    }

    /**
     * And an identity is declared here or read off the path, and never both.
     *
     * <p>A module of this compile takes the name over a module of the same name on the path, so what
     * is read off the path is what nothing here declares. Held because the lookup tries one and then
     * the other: with an identity in both, which arm a reader was answered with would be the order
     * the tries happen to be written in.
     */
    @Test
    void anIdentityIsNotBothDeclaredHereAndReadOffThePath() {
        CheckedData here = new CheckedData.Unit(named("demo", "Mode"));

        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> new CheckedProgram(List.of(module("demo", here)), List.of(),
                        Set.of(named("demo", "Mode"))));

        assertEquals("`demo.Mode` is declared here and read off the path", refused.getMessage());
    }

    private static TypeSymbol.AtModule named(String module, String name) {
        return TypeSymbols.declared(new TypeKey(module, name));
    }

    private static CheckedModule module(String name, CheckedData declares) {
        return new CheckedModule(name, List.of(), List.of(), List.of(declares));
    }
}
