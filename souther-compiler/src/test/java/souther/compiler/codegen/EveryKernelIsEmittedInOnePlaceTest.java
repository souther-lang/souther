package souther.compiler.codegen;

import souther.compiler.core.Kernel;

import org.junit.jupiter.api.Test;

import java.util.EnumSet;
import java.util.LinkedHashSet;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Every kernel the language has is emitted by this backend, and in one place.
 *
 * <pre>{@code
 *   Kernel = what the JVM's table emits ⊎ what BodyGen writes out
 * }</pre>
 *
 * <p>That a kernel is declared is not asked here any more. The library refuses to finish while a
 * constant of {@link Kernel} is declared nowhere and while a written key names no constant
 * ({@code stdlib.Stdlib.Builder#freeze}), so a compilation that runs at all has crossed both ways
 * already. What is left is a question about this backend: which kernels it answers, and whether it
 * answers each of them once.
 *
 * <p>What each side holds is asked of that side. A list of the written-out kernels kept here would
 * be a second statement of what the backend does, and would go on passing on the day the backend
 * stopped doing it.
 */
class EveryKernelIsEmittedInOnePlaceTest {

    @Test
    void everyKernelIsEmittedByTheTableOrWrittenOutInTheBackend() {
        Set<Kernel> unanswered = EnumSet.allOf(Kernel.class);
        unanswered.removeAll(Intrinsics.kernels());
        unanswered.removeAll(BodyGen.WRITTEN_OUT);

        assertEquals(Set.of(), unanswered, "the JVM emits nothing for these kernels");
    }

    /**
     * And no kernel is emitted twice.
     *
     * <p>The half a covering cannot see. A union covers a kernel held on both sides as readily as
     * one held on either, so a row added for something the backend already writes out passes it —
     * and the emitter would go on running its own arm, with the row it disagrees with sitting there
     * unread.
     */
    @Test
    void noKernelIsBothWrittenOutAndHeldInTheTable() {
        Set<Kernel> both = new LinkedHashSet<>(BodyGen.WRITTEN_OUT);
        both.retainAll(Intrinsics.kernels());

        assertEquals(Set.of(), both,
                "the backend writes these out and the table holds them too");
    }
}
