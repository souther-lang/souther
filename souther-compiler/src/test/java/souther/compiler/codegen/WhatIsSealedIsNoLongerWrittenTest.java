package souther.compiler.codegen;

import souther.compiler.Emitted;
import souther.compiler.EmittedBytes;
import souther.compiler.jvm.ClassFileImage;
import souther.compiler.jvm.GeneratedClass;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import org.junit.jupiter.api.Test;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where the classes of a module stop being writable, which is the one boundary between the thing
 * that is built and the value it comes to.
 *
 * <p>A class is emitted, instrumented and written onto, and every one of those replaces an array
 * with another. {@link Emissions#seal} is where that ends. Held to here rather than to the order
 * statements happen to be in: a stamping step appended after the sealing would otherwise be a
 * reader holding one thing and the next reader holding another, with nothing to say so.
 */
class WhatIsSealedIsNoLongerWrittenTest {

    private static final GeneratedClass.Value QUOTE =
            new GeneratedClass.Value(TypeSymbols.declared(new TypeKey("demo", "Quote")));
    private static final GeneratedClass.Lambda LAMBDA = new GeneratedClass.Lambda("demo", 0);

    private static Emissions written() {
        Emissions out = new Emissions("demo");
        out.put(QUOTE, EmittedBytes.of(QUOTE, "first"));
        return out;
    }

    @Test
    void whatIsWrittenBeforeItIsSealedIsWhatItAnswersWith() {
        Emissions out = written();
        out.rewrite(QUOTE, _ -> EmittedBytes.of(QUOTE, "rewritten"));

        assertEquals(Map.of(Emitted.value("demo", "Quote"),
                        ClassFileImage.of(EmittedBytes.of(QUOTE, "rewritten"))),
                out.seal());
    }

    @Test
    void nothingIsEmittedAfterwards() {
        Emissions out = written();
        out.seal();

        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> out.put(LAMBDA, EmittedBytes.of(LAMBDA)));
        assertTrue(refused.getMessage().contains("sealed"), refused.getMessage());
    }

    @Test
    void norAWholeSetOfThem() {
        Emissions out = written();
        out.seal();

        assertThrows(IllegalStateException.class,
                () -> out.putAll(Map.of(LAMBDA, EmittedBytes.of(LAMBDA))));
    }

    @Test
    void norIsAnythingWrittenOntoWhatIsThere() {
        Emissions out = written();
        out.seal();

        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> out.rewrite(QUOTE, _ -> EmittedBytes.of(QUOTE, "afterwards")));
        assertTrue(refused.getMessage().contains("sealed"), refused.getMessage());
    }

    /**
     * And the second reader is handed what the first was.
     *
     * <p>Built once and kept, rather than read off the arrays again: an array still reachable from
     * inside that somebody wrote into would otherwise reach the second reader and not the first,
     * which is the fault the sealing exists to make impossible said one way further down.
     */
    @Test
    void everyReaderIsHandedTheOneAnswer() {
        Emissions out = written();

        assertSame(out.seal(), out.seal());
    }
}
