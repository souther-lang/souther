package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.test.Nightly;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.atomic.AtomicReference;

import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * A chain of newtypes, one to a module, each wrapping the one in the module before, compiles on a
 * small stack.
 *
 * <p>One newtype to a module puts a module boundary at every link, so no reading of one module's
 * declarations reaches more than one of them, and what is left to follow the chain is the code each
 * module's classes are emitted by. A newtype's decoder is generated knowing only what the type it
 * wraps is handed; if it asked that of the end of the chain instead, the emitter would walk the
 * chain once per module, on the call stack, and run out of this one.
 *
 * <p>Asked once a night. A compile of a module chain costs more than its length beside the codecs,
 * so a chain long enough to run out of this stack takes seconds, and a shorter one fits on any stack
 * a thread can be given and still compile. What a newtype's decoder is handed is held on every
 * change by {@link CompileNewtypeTest}, which reads it off the generated signature; a walk to the
 * end of the chain coming back by another route is found by the morning.
 */
@Nightly
class AChainOfNewtypesAcrossModulesIsNotWalkedOnTheCallStackTest {

    private static final long STACK = 160L << 10;

    private static final int LINKS = 600;

    @Test
    void aChainOfModulesEachWrappingTheNewtypeBeforeOverAnObject() {
        List<String> modules = new ArrayList<>();
        modules.add("module m1 exposing ( T1 )\n\ndata T1 = { x: Int }\n");
        for (int i = 2; i <= LINKS; i++) {
            modules.add("module m" + i + " exposing ( T" + i + " )\n\nimport m" + (i - 1)
                    + " ( T" + (i - 1) + " )\n\ndata T" + i + " = T" + (i - 1) + "\n");
        }
        AtomicReference<Throwable> failed = new AtomicReference<>();
        Thread compiling = new Thread(null, () -> {
            try {
                Compiler.compileModules(modules);
            } catch (Throwable e) {
                failed.set(e);
            }
        }, "a small stack", STACK);
        compiling.start();
        try {
            compiling.join();
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            throw new AssertionError(e);
        }
        assertNull(failed.get(), () -> String.valueOf(failed.get()));
    }
}
