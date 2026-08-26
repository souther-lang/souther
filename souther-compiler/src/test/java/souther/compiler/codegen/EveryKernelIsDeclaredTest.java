package souther.compiler.codegen;

import souther.compiler.DefaultStdlib;
import souther.compiler.core.Kernel;

import org.junit.jupiter.api.Test;

import java.util.EnumSet;
import java.util.LinkedHashSet;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Every kernel the library ships is described by a declaration (ADR-0053), every kernel this
 * compiler has a name for is one of them, and each is emitted in one place. The signature lives in a
 * core module and the compiler holds only what a declaration cannot say — a kind, an ordering, the
 * branch a partial division emits.
 *
 * <p>Asked as a correspondence rather than as "the table of signatures is empty": an emitter added
 * without a declaration is a function that can be called and whose type nothing states, which is
 * what the table of signatures was.
 *
 * <p>Three sets, and they are one set, split in two:
 *
 * <pre>{@code
 *   Kernel = what the library declares = what the JVM's table emits ⊎ what BodyGen writes out
 * }</pre>
 *
 * <p>The vocabulary lives in two places on purpose — the {@code .sou} declarations say what an
 * operation takes and answers, {@link Kernel} is what a checked program carries it as — and this is
 * what makes the two one vocabulary rather than two that are meant to agree.
 *
 * <p>What each side holds is asked of that side. A list of the written-out kernels kept here would
 * be a second statement of what the backend does, and would go on passing on the day the backend
 * stopped doing it.
 */
class EveryKernelIsDeclaredTest {

    @Test
    void everyEmittedKernelHasADeclarationNamingIt() {
        Set<Kernel> emittedWithNoDeclaration = new LinkedHashSet<>(Intrinsics.kernels());
        emittedWithNoDeclaration.removeAll(declared());

        assertEquals(Set.of(), emittedWithNoDeclaration,
                "a kernel is emitted that no declaration describes");
    }

    @Test
    void everyDeclaredKernelHasAnEmitterOrIsWrittenOutInTheBackend() {
        Set<Kernel> declaredWithNoEmitter = new LinkedHashSet<>();
        for (Kernel kernel : declared()) {
            if (!Intrinsics.kernels().contains(kernel) && !BodyGen.WRITTEN_OUT.contains(kernel)) {
                declaredWithNoEmitter.add(kernel);
            }
        }

        assertEquals(Set.of(), declaredWithNoEmitter,
                "a kernel is declared that nothing emits");
    }

    /**
     * And no kernel is emitted twice.
     *
     * <p>The half the two above cannot see. A union covers a kernel held on both sides as readily as
     * one held on either, so a row added for something the backend already writes out passes them
     * both — and the emitter would go on running its own arm, with the row it disagrees with sitting
     * there unread.
     */
    @Test
    void noKernelIsBothWrittenOutAndHeldInTheTable() {
        Set<Kernel> both = new LinkedHashSet<>(BodyGen.WRITTEN_OUT);
        both.retainAll(Intrinsics.kernels());

        assertEquals(Set.of(), both,
                "the backend writes these out and the table holds them too");
    }

    /**
     * And every kernel this compiler names is declared.
     *
     * <p>The direction the others do not hold. A key a declaration writes that {@link Kernel} has no
     * constant for is refused while the library is built, so a compilation that runs at all has
     * crossed that way already; a constant with no declaration behind it is a kernel a checked
     * program could be said to reach and no signature describes, and nothing else would say so.
     */
    @Test
    void everyKernelThisCompilerNamesIsDeclared() {
        assertEquals(EnumSet.allOf(Kernel.class), declared(),
                "a kernel this compiler names is declared by no core module");
    }

    /** The kernels the library's declarations name. */
    private static Set<Kernel> declared() {
        return DefaultStdlib.get().intrinsics().keySet();
    }
}
