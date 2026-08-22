package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.ast.Hir;
import souther.compiler.check.BehaviorImplementation;
import souther.compiler.check.Prepared;
import souther.compiler.diag.CompileException;
import souther.compiler.query.Bodies;
import souther.compiler.query.Shapes;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.lang.classfile.ClassFile;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A behavior with no {@code let} is one of two things, and until now the compiler read one fact for
 * both: something a Java implementation supplies, or something whose {@code let} has not been
 * written yet. The two agree everywhere except where the behavior declares {@code depends on} — an
 * injection target may not, so a model written example-first had nowhere to put a row.
 *
 * <p>What decides is the clause. A behavior declaring {@code depends on} takes its dependencies as
 * arguments of a {@code let}, so it is a Souther implementation, and one with no {@code let} is a
 * Souther implementation nobody has written. Its name exists, rows against it wait, and nothing may
 * be generated that needs the body it has not got.
 */
class ABehaviorNobodyHasWrittenYetIsNotAnInjectionTargetTest {

    private static final String HEAD = """
            module example.owed exposing ( Id, Out, inner, outer )

            data Id = { n: Int }
            data Out = { n: Int }

            behavior inner : (id: Id) -> Out
            """;

    /** The arrangement issue #936 opens with: the rows are down, the body is not. */
    private static final String OWED = HEAD + """
            behavior outer : (id: Id) -> Out
                depends on inner

            example outer
                | (Id { n = 1 }) -> Out { n = 2 }
            """;

    @Test
    void aBehaviorMayDeclareWhatItDependsOnBeforeItsLetIsWritten() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of(OWED)));
    }

    @Test
    void itsRowsWaitForTheLetTheWayAnyUnwrittenBehaviorsDo() {
        Compilation compilation = Compilation.ofSource(OWED, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();

        AdequacyReport.BehaviorReport outer = AdequacyReport.of(compilation)
                .modules().get(0).behaviors().stream()
                .filter(b -> b.name().equals("outer")).findFirst().orElseThrow();

        assertEquals(1, outer.pending(), "the row waits for the `let`");
    }

    /**
     * Nothing a Java implementation could extend. An injection target is emitted as an abstract base
     * with a protected constructor; this is not one, and emitting the base would say Java may supply
     * a behavior whose dependencies Souther is the one that passes.
     */
    @Test
    void nothingIsEmittedForJavaToExtend() {
        Map<String, byte[]> classes = Compiler.compileModules(List.of(OWED));

        assertFalse(classes.containsKey(Emitted.impl("example.owed", "outer")),
                "no implementation was written, so none is emitted");
        var outer = ClassFile.of().parse(classes.get(Emitted.behaviorInterface("example.owed", "outer")));
        assertTrue(outer.flags().has(java.lang.reflect.AccessFlag.INTERFACE),
                "an unwritten behavior is not an abstract base a Java implementation extends");
    }

    /** The graph is the specification, and a specification may name what nobody has written. */
    @Test
    void anotherBehaviorMayRestOnItWhileItIsStillUnwritten() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of(HEAD + """
                behavior outer : (id: Id) -> Out
                    depends on inner

                behavior whole : (id: Id) -> Out
                    depends on outer
                """)));
    }

    /**
     * The state crosses the module boundary.
     *
     * <p>What is published carries no {@code let}, so an importer that worked this out again would
     * have the two body-less states to sort one declaration into and would take this one for an
     * injection target — and be told it may hand an implementation in.
     */
    @Test
    void anImporterIsToldWhichOfTheTwoBodylessStatesItIs() {
        List<String> declaring = List.of(HEAD + """
                behavior outer : (id: Id) -> Out
                    depends on inner
                """);

        assertDoesNotThrow(() -> Compiler.compileModules(withUpstream(declaring, """
                module example.reader exposing ( whole )
                import example.owed ( Id, Out )
                behavior whole : (id: Id) -> Out
                    depends on example.owed.outer
                """)));

        CompileException refused = assertThrows(CompileException.class,
                () -> Compiler.compileModules(withUpstream(declaring, """
                        module example.reader exposing ( whole )
                        import example.owed ( Id, Out )
                        behavior whole : (id: Id) -> Out
                            depends on example.owed.outer
                        let whole (id, outer) = outer(id)
                        """)));

        assertEquals("E1627", refused.code(), refused.getMessage());
    }

    /**
     * The two representations answer alike.
     *
     * <p>The rule is one method, and a behavior is read in two trees — the module as parsed, which is
     * what a reader off the path gets, and the lowered one the checks and the emitter walk. Each has
     * an adapter that asks the rule, and nothing else would notice if the adapters stopped agreeing:
     * whichever of them a consumer happened to ask would be its answer.
     */
    @Test
    void bothRepresentationsGiveOneAnswerForEveryBehavior() {
        String source = HEAD + """
                behavior outer : (id: Id) -> Out
                    depends on inner

                behavior whole : (id: Id) -> Out
                    depends on outer

                behavior twice : (id: Id) -> Out
                    constructs Out
                let twice (id) = Out { n = id.n * 2 }

                behavior chained = twice >-> twice
                """;
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();

        Map<String, BehaviorImplementation> asParsed = compilation.db()
                .ask(new Bodies.Implementation("example.owed")).value();
        Prepared lowered = compilation.db().ask(new Shapes.Prepared("example.owed")).value();

        Map<String, BehaviorImplementation> asLowered = new java.util.LinkedHashMap<>();
        for (Hir.BehaviorDef declared : lowered.behaviors()) {
            asLowered.put(declared.name(), lowered.implementationOf(declared));
        }

        assertEquals(asParsed, asLowered);
        assertEquals(BehaviorImplementation.UNIMPLEMENTED, asParsed.get("outer"));
        assertEquals(BehaviorImplementation.INJECTION_TARGET, asParsed.get("inner"));
        assertEquals(BehaviorImplementation.IMPLEMENTED, asParsed.get("twice"));
        assertEquals(BehaviorImplementation.IMPLEMENTED, asParsed.get("chained"));
    }

    private static List<String> withUpstream(List<String> upstream, String reader) {
        List<String> all = new java.util.ArrayList<>(upstream);
        all.add(reader);
        return all;
    }

    /** Where a body would have to call it, there is nothing to call. */
    @Test
    void abodyThatWouldHaveToCallItIsRefused() {
        CompileException refused = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(HEAD + """
                        behavior outer : (id: Id) -> Out
                            depends on inner

                        behavior whole : (id: Id) -> Out
                            depends on outer
                        let whole (id, outer) = outer(id)
                        """)));

        assertEquals("E1627", refused.code(), refused.getMessage());
    }
}
