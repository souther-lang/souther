package souther.compiler.codegen;

import souther.compiler.Emitted;
import souther.compiler.EmittedBytes;
import souther.compiler.generated.ProbeImage;
import souther.compiler.jvm.ClassFileImage;
import souther.compiler.jvm.GeneratedClass;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.TestFactory;

import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.function.Consumer;
import java.util.stream.Stream;

import static org.junit.jupiter.api.DynamicTest.dynamicTest;
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
        Emissions out = new Emissions("demo", new ProbeImage.Uninstrumented());
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

    /**
     * Every way of writing, each asked after the sealing.
     *
     * <p>Named one at a time and held to covering the type, which is the point of the row below it:
     * a way in that arrives without a line here is one nothing asked, and the guard that was
     * forgotten on it is the guard nothing says is missing.
     *
     * <p><b>What is refused is asking, not a write that had something in it.</b> A set with nothing
     * in it is here for that: {@code putAll} used to be the loop and nothing else, so a caller
     * handing over nothing walked past the guard — and what that guard held was "one class was
     * written after the sealing", which is not the rule.
     */
    private static Map<String, Consumer<Emissions>> everyWayOfWriting() {
        Map<String, Consumer<Emissions>> ways = new LinkedHashMap<>();
        ways.put("put", out -> out.put(LAMBDA, EmittedBytes.of(LAMBDA)));
        ways.put("putAll", out -> out.putAll(Map.of(LAMBDA, EmittedBytes.of(LAMBDA))));
        ways.put("putAll, of nothing", out -> out.putAll(Map.of()));
        ways.put("rewrite", out -> out.rewrite(QUOTE, _ -> EmittedBytes.of(QUOTE, "afterwards")));
        return ways;
    }

    /**
     * What this holds beside writing: what it was written for, whose numbers a run through it
     * leaves, and the sealing itself.
     *
     * <p>{@code probes} is settled when the classes are first asked for and never afterwards — it is
     * what the generation numbered, and a generation numbers once. So there is no write for the
     * sealing to refuse, and no order of calls under which two readers are told different things.
     */
    private static final Set<String> WHICH_DO_NOT_WRITE = Set.of("implemented", "probes", "seal");

    @TestFactory
    Stream<DynamicTest> everyWayOfWritingIsRefusedAfterwards() {
        return everyWayOfWriting().entrySet().stream().map(way -> dynamicTest(way.getKey(), () -> {
            Emissions out = written();
            out.seal();

            IllegalStateException refused =
                    assertThrows(IllegalStateException.class, () -> way.getValue().accept(out));
            assertTrue(refused.getMessage().contains("sealed"), refused.getMessage());
        }));
    }

    /**
     * And the ways above are the ways there are.
     *
     * <p>The list is a list somebody wrote, so what makes it a rule is being held to what the type
     * declares. A method arriving here fails until whoever wrote it says which of the two it is: a
     * way of writing, which is then asked after the sealing, or one of the things that do not write.
     */
    @Test
    void andThoseAreTheWaysIn() {
        Set<String> declared = Stream.of(Emissions.class.getDeclaredMethods())
                .filter(m -> !m.isSynthetic() && !Modifier.isPrivate(m.getModifiers()))
                .map(Method::getName)
                .collect(java.util.stream.Collectors.toCollection(java.util.TreeSet::new));
        Set<String> said = new java.util.TreeSet<>(WHICH_DO_NOT_WRITE);
        everyWayOfWriting().keySet().forEach(way -> said.add(way.split(",")[0]));

        assertEquals(said, declared,
                "every method of Emissions is a way of writing that is refused after the sealing,"
                        + " or is written down as one that does not write");
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

    /**
     * And what they are handed is not writable either.
     *
     * <p>Beside the row above rather than covered by it. One map handed to everybody is one map for
     * a reader to write into, and every reader after it would be handed what that reader made of it
     * — the refusals above say nothing about that, and neither does two readers getting the same
     * object.
     */
    @Test
    void norIsWhatTheyAreHandedWritable() {
        Map<String, ClassFileImage> sealed = written().seal();

        assertThrows(UnsupportedOperationException.class, sealed::clear);
        assertThrows(UnsupportedOperationException.class,
                () -> sealed.put(Emitted.value("demo", "Quote"), null));
    }
}
