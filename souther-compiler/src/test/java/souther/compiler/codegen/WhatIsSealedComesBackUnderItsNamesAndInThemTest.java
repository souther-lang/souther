package souther.compiler.codegen;

import org.junit.jupiter.api.Test;

import souther.compiler.EmittedBytes;
import souther.compiler.generated.ProbeImage;
import souther.compiler.jvm.ClassFileImage;
import souther.compiler.jvm.GeneratedClass;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The order the classes a generation answers with come back in.
 *
 * <p>What order they were emitted in is a fact about how the generation ran. Two generations that
 * emitted the same classes either way round answer the same thing, and the mapping they answer with
 * is keyed by name and cannot tell the two apart — so an order taken off it is one no equality of
 * the answer can disagree with. They come back under their names and in them.
 */
class WhatIsSealedComesBackUnderItsNamesAndInThemTest {

    @Test
    void theOrderTheClassesWereEmittedInIsNoPartOfTheAnswer() {
        assertEquals(List.copyOf(sealedAfterEmitting("Zed", "Alpha").keySet()),
                List.copyOf(sealedAfterEmitting("Alpha", "Zed").keySet()),
                "the classes come back in one order whichever order they were emitted in");
        assertEquals(List.of("demo.Alpha", "demo.Zed"),
                List.copyOf(sealedAfterEmitting("Zed", "Alpha").keySet()),
                "and that order is their names', which is what they are keyed on");
    }

    private static Map<String, ClassFileImage> sealedAfterEmitting(String... declared) {
        Emissions out = new Emissions("demo", new ProbeImage.Uninstrumented());
        for (String each : declared) {
            GeneratedClass.Value what =
                    new GeneratedClass.Value(TypeSymbols.declared(new TypeKey("demo", each)));
            out.put(what, EmittedBytes.of(what, each));
        }
        return out.seal();
    }
}
