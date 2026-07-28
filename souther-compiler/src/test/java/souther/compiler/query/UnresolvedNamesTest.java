package souther.compiler.query;

import souther.compiler.Compiler;
import souther.compiler.diag.Diagnostic;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A name that denotes nothing is reported and the compiler carries on.
 *
 * <p>It denotes an error type instead of ending the module. That type absorbs, so the one mistake is
 * reported once rather than again at every position the value it produced flowed into — and the rest
 * of the module is read, so an author is told about every unknown name at once instead of one per
 * compile.
 */
class UnresolvedNamesTest {

    private static List<Diagnostic> diagnose(String source) {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("a.sou", source);
        return Compiler.diagnoseModules(byId, Set.of()).get("a.sou");
    }

    @Test
    void everyUnknownNameIsReportedAtOnce() {
        List<Diagnostic> found = diagnose("""
                module m.a

                data A = { one: Nowhere, two: Elsewhere }
                """);

        assertEquals(2, found.size(), "both, not the first: " + found);
        assertTrue(found.stream().anyMatch(d -> d.args() != null
                && List.of(d.args()).contains("Nowhere")));
        assertTrue(found.stream().anyMatch(d -> d.args() != null
                && List.of(d.args()).contains("Elsewhere")));
    }

    @Test
    void oneMistakeIsNotReportedAtEveryPlaceTheValueWent() {
        // `total` has no type, so every position it flows into could disagree with it. None does:
        // an error type is assignable both ways.
        List<Diagnostic> found = diagnose("""
                module m.a exposing ( Order, price )

                data Order = { total: Nowhere }

                behavior price : (o: Order) -> Int
                let price (o) = o.total
                """);

        assertEquals(1, found.size(), "the unknown name, and nothing downstream of it: " + found);
    }

    @Test
    void aModuleWithATypeNobodyCanNameEmitsNothing() {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("a.sou", """
                module m.a

                data A = { one: Nowhere }
                """);
        Compilation c = Compilation.ofDocuments(byId, Set.of(),
                souther.compiler.meta.ModulePath.EMPTY);
        c.diagnostics();

        assertEquals(Map.of(), c.classes(),
                "there is no bytecode for a type nobody could name");
    }
    @Test
    void anUnknownNameInABodyAlsoStopsTheModuleBeingEmitted() {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("a.sou", """
                module m.a exposing ( A, f )

                data A = { n: Int }

                behavior f : (n: Int) -> A
                    constructs A
                let f (n) = Nowhere { n = n }
                """);
        Compilation c = Compilation.ofDocuments(byId, Set.of(),
                souther.compiler.meta.ModulePath.EMPTY);
        List<Diagnostic> found = c.diagnostics().get("a.sou");

        assertEquals(1, found.size(),
                "the name that denotes nothing, and nothing about constructing it: " + found);
        assertTrue(found.stream().anyMatch(d -> "check.unknown.type.msg".equals(d.messageKey())),
                "the construction names nothing, and that is said: " + found);
        assertEquals(Map.of(), c.classes(),
                "a construction of a type nobody could name is not emitted");
    }

    @Test
    void abandoningOneDefinitionStillChecksTheOthers() {
        // `f` rests on a name that denotes nothing, so there is nothing to say about what it does.
        // `g` is a different definition and is wrong in its own right.
        List<Diagnostic> found = diagnose("""
                module m.a exposing ( A, f, g )

                data A = { n: Int }

                behavior f : (n: Int) -> A
                    constructs A
                let f (n) = Nowhere { n = n }

                behavior g : (n: Int) -> Int
                let g (n) = "not an Int"
                """);

        assertEquals(2, found.size(),
                "the unknown name, and g's own mistake — nothing about what f does: " + found);
        assertTrue(found.stream().anyMatch(d -> "check.unknown.type.msg".equals(d.messageKey())),
                "the name that denotes nothing: " + found);
        assertTrue(found.stream().anyMatch(d -> d.diff() != null),
                "and a type mismatch in the definition that has one: " + found);
    }

    /**
     * The same, for a name in the value namespace. A stage that names no behavior is one definition's
     * mistake, and the definitions around it are checked as they would be without it.
     */
    @Test
    void anUnknownBehaviorInAPipelineStillLetsTheOtherDefinitionsBeChecked() {
        List<Diagnostic> found = diagnose("""
                module m.a exposing ( f, p, g )

                behavior f : (n: Int) -> Int
                let f (n) = n

                behavior p = f >-> nosuch

                behavior g : (n: Int) -> Int
                let g (n) = "not an Int"
                """);

        assertEquals(2, found.size(),
                "the unknown behavior, and g's own mistake: " + found);
        assertTrue(found.stream().anyMatch(d -> "check.unknown.behavior.msg".equals(d.messageKey())),
                "the stage that names no behavior: " + found);
        assertTrue(found.stream().anyMatch(d -> d.diff() != null),
                "and the type mismatch in the definition that has one: " + found);
    }

    /** A stage that names nothing is pointed at where it is written, not at the whole behavior. */
    @Test
    void anUnknownStageIsReportedAtTheStage() {
        List<Diagnostic> found = diagnose("""
                module m.a exposing ( f, p )

                behavior f : (n: Int) -> Int
                let f (n) = n

                behavior p = f >-> nosuch
                """);

        assertEquals(1, found.size(), found.toString());
        assertEquals(6, found.get(0).region().start().line(), found.toString());
        assertEquals(20, found.get(0).region().start().column(),
                "the stage, not the behavior it is in: " + found);
    }

    /** A composition resting on a stage that names nothing has no meaning to emit, and neither has
     * the module it is in. */
    @Test
    void aModuleWithAStageThatNamesNothingEmitsNothing() {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("a.sou", """
                module m.a exposing ( f, p )

                behavior f : (n: Int) -> Int
                let f (n) = n

                behavior p = f >-> nosuch
                """);
        Compilation c = Compilation.ofDocuments(byId, Set.of(),
                souther.compiler.meta.ModulePath.EMPTY);
        c.diagnostics();

        assertEquals(Map.of(), c.classes(),
                "there is no bytecode for a composition nobody could resolve");
    }

    /** The same, where the stage names a module this compilation does not have. */
    @Test
    void aStageInAModuleNobodyHasStillLetsTheOtherDefinitionsBeChecked() {
        List<Diagnostic> found = diagnose("""
                module m.a exposing ( f, p, g )

                behavior f : (n: Int) -> Int
                let f (n) = n

                behavior p = nosuch.h >-> f

                behavior g : (n: Int) -> Int
                let g (n) = "not an Int"
                """);

        assertEquals(2, found.size(),
                "the stage nobody declares, and g's own mistake: " + found);
        assertTrue(found.stream().anyMatch(d -> d.diff() != null),
                "and the type mismatch in the definition that has one: " + found);
    }

    /**
     * The same as {@link #abandoningOneDefinitionStillChecksTheOthers}, with the unknown name in a
     * declaration rather than in a body. Where the name is written must not decide whether the rest
     * of the module is checked.
     */
    @Test
    void anUnknownTypeInADeclarationStillLetsTheOtherDefinitionsBeChecked() {
        List<Diagnostic> found = diagnose("""
                module m.a exposing ( A, g )

                data A = { value: Nowhere }

                behavior g : (n: Int) -> Int
                let g (n) = "not an Int"
                """);

        assertEquals(2, found.size(),
                "the unknown name, and g's own mistake: " + found);
        assertTrue(found.stream().anyMatch(d -> "check.unknown.type.msg".equals(d.messageKey())),
                "the name that denotes nothing: " + found);
        assertTrue(found.stream().anyMatch(d -> d.diff() != null),
                "and the type mismatch in the definition that has one: " + found);
    }
}
