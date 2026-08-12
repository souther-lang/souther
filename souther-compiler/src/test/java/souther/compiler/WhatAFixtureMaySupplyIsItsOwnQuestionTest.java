package souther.compiler;

import souther.compiler.examples.FixtureShape;
import souther.compiler.check.Sig;
import souther.compiler.diag.CompileException;
import souther.compiler.query.Compilation;
import souther.compiler.check.BoundaryInput;
import souther.compiler.types.Type;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
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

    /**
     * A key is a position of the same kind as a value, in the neutral form as well as in the
     * classification. An inner collection written in key position is that collection's neutral form
     * and not the list of pairs it was written as — which the shaping left alone while admitting it,
     * so the shape said yes and the decode said {@code not_a_map}.
     */
    @Test
    void aMapKeyIsShapedLikeAnythingElseAtThatPosition() {
        assertDoesNotThrow(() -> Compiler.compile(HEAD + """
                let sizeOfNested (m: Map<Map<Int, Int>, Int>) : Int = Map.size(m)
                example f
                  | "a map keys a map" : (sizeOfNested(Map.fromList([ (Map.fromList([ (1, 2) ]), 3) ]))) -> Out { n = 1 }
                """));
        assertDoesNotThrow(() -> Compiler.compile(HEAD + """
                let deep (m: Map<List<Map<Int, Int>>, Int>) : Int = Map.size(m)
                example f
                  | "and at depth" : (deep(Map.fromList([ ([ Map.fromList([ (1, 2) ]) ], 3) ]))) -> Out { n = 1 }
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
     * A codec is derived for what a module of this compilation declared and for nothing else, which
     * is one answer the symbol table already holds. A rounding mode is the language's own, so
     * nothing derived one for it — and that is a fact about the type, where the old refusal reported
     * a reflective lookup that came back empty, which is a fact about how the reader went looking.
     */
    @Test
    void aTypeTheLanguageDeclaresIsRefusedForHavingNoDerivedCodec() {
        CompileException e = err(HEAD + """
                let scaled (m: RoundingMode) : Int = 1
                example f
                  | "r" : (scaled(HALF_UP)) -> Out { n = 1 }
                """);
        assertTrue(e.getMessage().contains("declared by the language"), e.getMessage());
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
     * What a module of this compilation declared includes what it read off the path: a type an
     * imported module declares has a codec its own build derived, and a fixture builds through it.
     * The rule is one question to the symbol table, so this is the side of that line the wording
     * does not name.
     */
    @Test
    void aTypeAnImportedModuleDeclaresBuilds() {
        java.util.Map<String, byte[]> library = Compiler.compile("""
                module shared.money exposing ( Amount )
                data Amount = Int
                """);
        assertDoesNotThrow(() -> Compiler.compileModules(List.of("""
                module app.order
                import shared.money ( Amount )
                data Out = { n: Int }
                behavior place : (a: Amount) -> Out
                    constructs Out
                let place (a) = Out { n = a.value }
                example place
                  | "an imported type in a fixture" : (Amount(5)) -> Out { n = 5 }
                """), library::get));
    }

    /**
     * A position a behavior's boundary established carries its own admitted answer, and the reader
     * reads it rather than putting the type through this walk a second time. What makes that a
     * projection rather than a second decision is that every concrete type a boundary admits is one
     * a fixture admits — so there is nothing in the crossing that can refuse.
     *
     * <p>Concrete, because an answer of several types is not one shape: which of them a value is is
     * what the row writes, which is the row's claim and not the position's answer. That one is
     * {@link #anAnswerOfSeveralTypesIsNotOneShape}.
     *
     * <p>Asked of witnesses a compile produced, not of ones written here: what has to hold is about
     * the shapes a boundary actually builds.
     */
    @Test
    void everyConcreteShapeABoundaryAdmitsProjectsWithoutRefusing() {
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
        assertNotNull(FixtureShape.ofWholeAnswer(sig.out()));
    }

    /**
     * And an answer of several types is not one shape. The projection says so rather than raising:
     * a row states a value of one of them, and it is built against the case it names.
     */
    @Test
    void anAnswerOfSeveralTypesIsNotOneShape() {
        Compilation compilation = Compiler.compiled("""
                module demo

                data Adult = { name: String }
                data Minor = { age: Int }

                behavior classify : (age: Int) -> Adult | Minor
                    constructs Adult, Minor
                let classify (age) = {
                    guard age >= 18 else Minor { age = age }
                    Adult { name = "adult" }
                }
                """, "demo", new ArrayList<>());
        Sig sig = compilation.signatures("demo").get("classify");

        assertNull(FixtureShape.ofWholeAnswer(sig.out()));

        // and a row against such a behavior states one of them, by naming it
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data Adult = { name: String }
                data Minor = { age: Int }

                behavior classify : (age: Int) -> Adult | Minor
                    constructs Adult, Minor
                let classify (age) = {
                    guard age >= 18 else Minor { age = age }
                    Adult { name = "adult" }
                }

                example classify
                  | "grown" : (20) -> Adult { name = "adult" }
                """));
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
