package souther.compiler.codegen;

import souther.compiler.DefaultStdlib;
import souther.compiler.core.KernelSignature;
import souther.compiler.types.Type;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A kernel's JVM descriptor belongs to the kernel, not to the call — the callee's declaration
 * decides it, and the arguments only supply values. {@link Intrinsics.DeclaredStatic} states that
 * directly, reading the declared signature; {@link Intrinsics.RuntimeStatic} builds a descriptor
 * from the types it observes at the call, and agrees with the declaration only where an observed
 * type cannot differ from the declared one.
 *
 * <p>That held by accident until a declared parameter took a sum: every value flowing into
 * {@code RoundingMode} is one of its cases, so the observed type named a case class and the
 * declaration named the sum, and the call linked to no such method (issue #270). The two happened
 * to agree everywhere else because every other parameter is either a primitive or a container —
 * whose boundary form the type fixes on its own — or a type variable in a slot the emitter erases
 * to {@code Object}, which is what the declaration would give.
 *
 * <p>This holds that shape rather than the coincidence. A declared parameter whose boundary form
 * depends on which value arrives — a reference, a type variable, a union — may not be read off the
 * call, so the entry taking one belongs on the declaration-reading emitter. Registering a second
 * runtime-backed data ({@code jvm.SoutherJvmAbi.providedByTheRuntime}) and writing it into a kernel's parameters is the move that
 * reproduces #270, and this is what stops it.
 */
class KernelDescriptorsComeFromDeclarationsTest {

    @Test
    void aKernelReadingItsDescriptorFromTheCallTakesNoTypeAValueCanNarrow() {
        List<String> readOffTheCall = new ArrayList<>();
        for (var entry : Intrinsics.emitters().entrySet()) {
            if (!(entry.getValue() instanceof Intrinsics.RuntimeStatic kernel)) {
                continue;
            }
            KernelSignature declared = DefaultStdlib.get().intrinsic(entry.getKey()).signature();
            for (int i = 0; i < declared.parameters().size(); i++) {
                // An erased slot is passed as Object whatever arrives, which is what the declared
                // type would give too, so the observed type cannot disagree there.
                if (kernel.objectSlots().contains(i)) {
                    continue;
                }
                Type param = declared.parameters().get(i);
                if (!fixesItsOwnBoundaryForm(param)) {
                    readOffTheCall.add(entry.getKey().key() + " parameter " + (i + 1)
                            + " is declared " + Type.show(param));
                }
            }
        }

        assertEquals(List.of(), readOffTheCall,
                "these kernels build a descriptor from the type observed at the call, for a"
                        + " parameter whose declared type a value can arrive narrower than — move"
                        + " them to DeclaredStatic, which reads the declaration");
    }

    /**
     * Whether the type alone settles the JVM type a value of it takes at a kernel boundary.
     *
     * <p>A primitive and a container do: every value of {@code Decimal} is a {@code BigDecimal} and
     * every value of {@code List<'a>} a {@code List}, whatever the element. A reference does not —
     * a value of a sum is one of its cases — and neither does a type variable or a union, whose
     * values are of the members. Listed rather than excluded so a type constructor added later is
     * failed here and considered, rather than defaulting into the safe half.
     */
    private static boolean fixesItsOwnBoundaryForm(Type t) {
        return t instanceof Type.Prim
                || t instanceof Type.ListOf
                || t instanceof Type.MapOf
                || t instanceof Type.SetOf
                || t instanceof Type.OptionOf;
    }
}
