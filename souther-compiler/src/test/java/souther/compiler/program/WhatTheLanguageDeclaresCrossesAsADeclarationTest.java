package souther.compiler.program;

import souther.compiler.DefaultStdlib;
import souther.compiler.core.Kernel;
import souther.compiler.core.KernelSignature;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import org.junit.jupiter.api.Test;

import java.util.EnumMap;
import java.util.List;
import java.util.Map;

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
     * One address belongs to one world.
     *
     * <p>Nothing of a compilation is in the reserved namespace, and a module of this compile takes
     * its name over one of the same name on the path, so the three never meet. Were two of them to,
     * whichever was filed last would silently be the answer every reader got, and nothing would say
     * the other had been there. Refused where the index is built, which is the one place all three
     * are in hand.
     */
    @Test
    void oneAddressBelongsToOneWorld() {
        CheckedData twice = new CheckedData.Unit(named("demo", "Mode"));

        assertEquals("`demo.Mode` is declared by A_MODULE and by THE_LANGUAGE",
                assertThrows(IllegalStateException.class, () -> new CheckedProgram(
                        List.of(module("demo", twice)), List.of(twice), List.of(), kernels()))
                        .getMessage());
        assertEquals("`demo.Mode` is declared by A_MODULE and by A_MODULE_ON_THE_PATH",
                assertThrows(IllegalStateException.class, () -> new CheckedProgram(
                        List.of(module("demo", twice)), List.of(), List.of(twice), kernels()))
                        .getMessage());
    }

    /** What the language declares its kernels to take, as an assembled program carries them. The
     *  fixtures below are about which world an address belongs to, so everything else about them is
     *  a program as one really is. */
    private static Map<Kernel, KernelSignature> kernels() {
        Map<Kernel, KernelSignature> declared = new EnumMap<>(Kernel.class);
        DefaultStdlib.get().intrinsics()
                .forEach((kernel, intrinsic) -> declared.put(kernel, intrinsic.signature()));
        return declared;
    }

    private static TypeSymbol.AtModule named(String module, String name) {
        return TypeSymbols.declared(new TypeKey(module, name));
    }

    private static CheckedModule module(String name, CheckedData declares) {
        return new CheckedModule(name, List.of(), List.of(), List.of(declares));
    }
}
