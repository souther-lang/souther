package souther.compiler.query;

import souther.compiler.Compiler;
import souther.compiler.DefaultStdlib;
import souther.compiler.jvm.ClassFileImage;
import souther.compiler.jvm.LinkageTarget;
import souther.compiler.meta.ModulePath;
import souther.compiler.meta.ModuleReadback;
import souther.compiler.meta.ReadableModule;
import souther.compiler.meta.Readback;
import souther.compiler.types.TypeKey;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * What a module records it was built against is what working out its projections and emitting its
 * classes read of other modules' declarations — asked of the recording directly, and not of a
 * compile that refuses something.
 *
 * <p>Each case is one a class file cannot show. A behavior taking one input is held as the runtime's
 * unary {@code Behavior}, so nothing in the constant pool names it; a helper another module
 * publishes is expanded where it is called, so what its body reads is read by the caller's classes
 * and not by the publisher's.
 */
class WhatAModuleIsBuiltAgainstIsWhatItReadTest {

    private static final String C = """
            module lib.c exposing ( rate, Base, other )
            behavior rate : (n: Int) -> Int
            data Base = { n: Int }
            behavior other : (n: Int) -> Int
            let other (n) = n
            """;

    /** `lib.b`'s own projections rest on `lib.c.rate`, which its `charged` holds, and on
     *  `lib.c.Base`, which its `Wrapped` lays out as a field. */
    private static final String B = """
            module lib.b exposing ( charged, Wrapped )
            import lib.c ( rate, Base )
            behavior charged : (n: Int) -> Int depends on rate
            let charged (n, rate) = rate(n)
            data Wrapped = { base: Base }
            """;

    /**
     * Working out what `lib.b` provides reads what its projections rest on and nothing else: the
     * number of inputs of the dependency it holds — which its classes keep as the unary
     * {@code Behavior} and never name — and the class of the type a field of its holds.
     */
    @Test
    void workingOutWhatAModuleProvidesReadsWhatItsProjectionsRestOn() {
        Compilation compilation = Compilation.ofSources(List.of(C, B), ModulePath.of(Map.of()));

        Linkages.Of provided = compilation.db().ask(new Linkages.Provided("lib.b")).value();

        assertEquals(Set.of(
                        new LinkageTarget.Behavior(new ValueName.Behavior("lib.c", "rate")),
                        new LinkageTarget.Data(new TypeKey("lib.c", "Base"))),
                provided.read().keySet(),
                "what lib.b's projections read of lib.c, and not lib.c.other");
    }

    /**
     * A helper `lib.p` publishes reads a value of `lib.d`. The helper is expanded where it is called,
     * so the reader's classes call `lib.d`'s entry and record it; `lib.p`'s own classes never run
     * the body and do not.
     */
    @Test
    void whatAPublishedHelpersBodyReadsIsWhatItsCallerIsBuiltAgainst() {
        Map<String, ClassFileImage> classes = new HashMap<>(Compiler.compile("""
                module lib.d exposing ( limit )
                let limit = List.length([1, 2, 3])
                """));
        classes.putAll(Compiler.compileModules(List.of("""
                module lib.p exposing ( capped )
                import lib.d ( limit )
                let capped (n: Int) = n + limit
                """), ModulePath.of(classes)));
        classes.putAll(Compiler.compileModules(List.of("""
                module app.r exposing ( use )
                import lib.p ( capped )
                behavior use : (n: Int) -> Int
                let use (n) = capped(n)
                """), ModulePath.of(classes)));
        LinkageTarget limit = new LinkageTarget.Value(new ValueName.Helper("lib.d", "limit"));

        assertEquals(Set.of(limit), readBack("app.r", classes).requires().keySet(),
                "app.r's classes call lib.d's entry the helper's body reads");
        assertEquals(Set.of(), readBack("lib.p", classes).requires().keySet(),
                "lib.p's classes never run the body they publish");
    }

    /**
     * A value another module declares runs there however the reader came by it: named directly, or
     * named by a helper a third module publishes. Each reading calls the declaring module's entry,
     * and none copies the value's body into the reader.
     */
    @Test
    void aValueReachedThroughAHelperIsReadAsTheValueNamedDirectlyIs() {
        Map<String, ClassFileImage> classes = new HashMap<>(Compiler.compile("""
                module lib.d exposing ( limit )
                let limit = List.length([1, 2, 3])
                """));
        classes.putAll(Compiler.compileModules(List.of("""
                module lib.p exposing ( capped )
                import lib.d ( limit )
                let capped (n: Int) = n + limit
                """), ModulePath.of(classes)));
        Map<String, ClassFileImage> direct = Compiler.compileModules(List.of("""
                module app.r exposing ( use )
                import lib.d ( limit )
                behavior use : (n: Int) -> Int
                let use (n) = n + limit
                """), ModulePath.of(classes));
        Map<String, ClassFileImage> throughAHelper = Compiler.compileModules(List.of("""
                module app.r exposing ( use )
                import lib.p ( capped )
                behavior use : (n: Int) -> Int
                let use (n) = capped(n)
                """), ModulePath.of(classes));

        assertEquals(readBack("app.r", direct).requires(),
                readBack("app.r", throughAHelper).requires());
    }

    private static ReadableModule readBack(String module, Map<String, ClassFileImage> classes) {
        return assertInstanceOf(ReadableModule.class, assertInstanceOf(Readback.Ready.class,
                ModuleReadback.read(module, ModulePath.of(classes).declarations(),
                        DefaultStdlib.get().names())).value());
    }
}
