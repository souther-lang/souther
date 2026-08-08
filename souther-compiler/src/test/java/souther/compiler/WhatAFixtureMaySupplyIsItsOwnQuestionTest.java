package souther.compiler;

import souther.compiler.check.Sig;
import souther.compiler.diag.CompileException;
import souther.compiler.query.Compilation;
import souther.compiler.types.BoundaryInput;
import souther.compiler.types.Type;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A position a fixture supplies is a position of its own, and what may stand there is what a decoder
 * reads: a scalar, a type whose codec was derived, or a collection of them.
 *
 * <p>It used to be worked out as the reader went, from three things that are not that question — the
 * boundary's rule about what may key a {@code Map} that crosses, whether reflection found a
 * generated {@code decoder()}, and which constructors of {@code Type} the reader had a branch for.
 * The rows below are the ones where those three disagreed with each other.
 */
class WhatAFixtureMaySupplyIsItsOwnQuestionTest {

    private static final String HEAD = """
            module demo
            data Out = { n: Int }
            behavior f : (n: Int) -> Out
                constructs Out
            let f (n) = Out { n = n }
            """;

    private static CompileException err(String model) {
        return assertThrows(CompileException.class, () -> Compiler.compile(model));
    }

    /**
     * A helper's {@code Map<Int, Int>} crosses nothing, and a fixture writes a map of the keys
     * themselves rather than the object of strings a boundary map crosses as. It was refused for
     * breaking the boundary's rule, which was the rule of somewhere else.
     */
    @Test
    void aMapAHelperTakesIsKeyedByWhateverADecoderReads() {
        assertDoesNotThrow(() -> Compiler.compile(HEAD + """
                let sizeOfMap (m: Map<Int, Int>) : Int = Map.size(m)
                example f
                  | "keyed by Int" : (sizeOfMap(Map.fromList([ (1, 2), (3, 4) ]))) -> Out { n = 2 }
                """));
    }

    /** And the kinds that already built go on building. */
    @Test
    void theCollectionsThatBuiltStillBuild() {
        assertDoesNotThrow(() -> Compiler.compile(HEAD + """
                data UserId = String
                let sizes (xs: List<Int>, s: Set<String>, m: Map<UserId, Int>) : Int = List.length(xs)
                example f
                  | "r" : (sizes([ 1 ], Set.fromList([ "a" ]), Map.fromList([ (UserId("u"), 2) ]))) -> Out { n = 1 }
                """));
    }

    /**
     * A type the runtime implements by hand belongs to no compiled module, so nothing derived a
     * codec for it. That is a fact about the type, and it is what the refusal says — it used to be
     * reported as a reflective lookup that came back empty, which is a fact about how the reader
     * went looking.
     */
    @Test
    void aTypeTheRuntimeImplementsIsRefusedForHavingNoDerivedCodec() {
        CompileException e = err(HEAD + """
                let scaled (m: RoundingMode) : Int = 1
                example f
                  | "r" : (scaled(HALF_UP)) -> Out { n = 1 }
                """);
        assertTrue(e.getMessage().contains("implemented by the runtime"), e.getMessage());
    }

    /**
     * {@code Raw} is spelled like a primitive and denotes a reference, which is why the reader's
     * {@code Raw} arm never ran: the name fell through to reflection and failed there. Refused for
     * being the reserved type now, wherever it is spelled.
     */
    @Test
    void theReservedTypeIsRefusedAsItself() {
        CompileException e = err(HEAD + """
                let asRaw (r: Raw) : Int = 1
                example f
                  | "r" : (asRaw(1)) -> Out { n = 1 }
                """);
        assertTrue(e.getMessage().contains("reserved type"), e.getMessage());
    }

    /** A tuple and a function have no external representation, so no decoder reads one. */
    @Test
    void aValueWithNoExternalRepresentationIsRefusedForHavingNone() {
        CompileException e = err(HEAD + """
                let firstOf (p: (Int, Int)) : Int = 1
                example f
                  | "r" : (firstOf((1, 2))) -> Out { n = 1 }
                """);
        assertTrue(e.getMessage().contains("no external representation"), e.getMessage());
    }

    /**
     * A position a behavior's boundary established carries its own admitted answer, and the reader
     * reads it rather than putting the type through this walk a second time. What makes that a
     * projection rather than a second decision is that every type a boundary admits is one a fixture
     * admits — so there is nothing in the crossing that can refuse.
     *
     * <p>Asked of witnesses a compile produced, not of ones written here: what has to hold is about
     * the shapes a boundary actually builds.
     */
    @Test
    void everyShapeABoundaryAdmitsIsOneAFixtureAdmits() {
        Compilation compilation = Compiler.compiled("""
                module demo

                data UserId = String
                data Note = { text: String? }
                data Day = HOLIDAY | WORKDAY

                behavior wide : (n: Int, s: String, b: Bool, d: Decimal, day: Date, at: DateTime,
                                 note: Note, ids: List<UserId>, seen: Set<String>,
                                 byName: Map<String, Note>, byId: Map<UserId, Int>,
                                 byDay: Map<Date, Int>, byKind: Map<Day, Int>) -> Note
                let wide (n, s, b, d, day, at, note, ids, seen, byName, byId, byDay, byKind) = note
                """, "demo", new ArrayList<>());
        Sig sig = compilation.signatures("demo").get("wide");

        for (BoundaryInput in : sig.ins()) {
            assertDoesNotThrow(() -> FixtureShape.of(in), Type.show(in.type()));
        }
        assertDoesNotThrow(() -> FixtureShape.of(sig.out()));
    }

    /**
     * An optional standing at the position itself is refused, and an optional a data holds is not
     * this rule's business at all: the walk stops at a nominal, and that data's own decoder reads
     * its {@code ?} field — which is why {@code None} goes on being written there.
     */
    @Test
    void anOptionalIsRefusedWhereItStandsAndNotWhereADataHoldsIt() {
        CompileException e = err(HEAD + """
                let orZero (o: Option<Int>) : Int = Option.withDefault(0, o)
                example f
                  | "r" : (orZero(None)) -> Out { n = 0 }
                """);
        assertTrue(e.getMessage().contains("absence belongs to the data that holds it"), e.getMessage());

        assertDoesNotThrow(() -> Compiler.compile("""
                module demo
                data Note = { text: String? }
                data Out = { n: Int }
                behavior f : (note: Note) -> Out
                    constructs Out
                let f (note) = Out { n = 1 }
                example f
                  | "absent" : (Note { text = None }) -> Out { n = 1 }
                """));
    }
}
