package souther.compiler;

import souther.compiler.check.Sig;
import souther.compiler.diag.CompileException;
import souther.compiler.query.Compilation;
import souther.compiler.check.BoundaryInput;
import souther.compiler.types.MapKeyRepresentation;
import souther.compiler.check.BoundaryOutput;
import souther.compiler.types.LeafScalar;

import souther.compiler.meta.ModulePath;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Making a behavior's signature is what admits what it carries, and there is no other way to make
 * one. So a phase below the check is handed the shapes a decoder and an encoder are built for, and a
 * type the boundary does not admit does not reach it — not because every reader knows which types
 * those are, but because the signature that would have carried one was never built.
 *
 * <p>Two things follow, and both are held here. A signature that exists classifies to those shapes,
 * whether it was written or composed. And a type the boundary refuses is reported by the obligation
 * that owns the position it stands in.
 */
class OneBoundaryAnswerReachesTheReaderTest {

    private static Sig sigOf(String source, String behavior) {
        Compilation compilation = Compiler.compiled(source, "demo", new ArrayList<>());
        return compilation.signatures("demo").get(behavior);
    }

    private static CompileException err(String source) {
        return assertThrows(CompileException.class, () -> Compiler.compile(source));
    }

    @Test
    void aSignatureIsTheShapesItsCodecsAreBuiltFor() {
        Sig sig = sigOf("""
                module demo

                data UserId = String
                data Note = { text: String }

                behavior f : (n: Int, ids: List<UserId>, seen: Set<String>, by: Map<UserId, Note>) -> Note
                let f (n, ids, seen, by) = Note { text = "x" }
                """, "f");

        assertEquals(4, sig.ins().size());
        assertEquals(LeafScalar.INT,
                assertInstanceOf(BoundaryInput.Scalar.class, sig.ins().get(0)).scalar());

        BoundaryInput.ListOf ids = assertInstanceOf(BoundaryInput.ListOf.class, sig.ins().get(1));
        assertEquals("UserId",
                assertInstanceOf(BoundaryInput.Nominal.class, ids.element()).name().name());

        BoundaryInput.SetOf seen = assertInstanceOf(BoundaryInput.SetOf.class, sig.ins().get(2));
        assertEquals(LeafScalar.STRING,
                assertInstanceOf(BoundaryInput.Scalar.class, seen.element()).scalar());

        // The key is the witness the map-key rule answers with, so a key position holds a kind rather
        // than a shape — a list or an option cannot be written there at all.
        BoundaryInput.MapOf by = assertInstanceOf(BoundaryInput.MapOf.class, sig.ins().get(3));
        assertEquals("UserId",
                assertInstanceOf(MapKeyRepresentation.NamedKey.class, by.key().representation()).name().name());
        assertInstanceOf(BoundaryInput.Nominal.class, by.value());

        assertEquals("Note", assertInstanceOf(BoundaryOutput.Nominal.class, sig.out()).name().name());
    }

    @Test
    void aUnionNobodyNamedIsAnOutputShapeAndNotAnInputOne() {
        Sig sig = sigOf("""
                module demo

                data Adult = { name: String }
                data Minor = { age: Int }

                behavior classify : (age: Int) -> Adult | Minor
                    constructs Adult, Minor
                let classify (age) = {
                    guard age >= 18 else Minor { age = age }
                    Adult { name = "adult" }
                }
                """, "classify");

        assertEquals(List.of("Adult", "Minor"), memberNames(sig.out()));
    }

    /**
     * A composition's answer is a type nobody wrote — the last stage's, merged with the cases that
     * left the main line — and it is a signature in the same sense as a declared one. Given only
     * declared ones a witness, a reader would need a way back to the type for the rest, which is the
     * question this removes.
     */
    @Test
    void aCompositionCarriesTheSameAnswerAsADeclaredBehavior() {
        Sig sig = sigOf("""
                module demo

                data In = { n: Int }
                data Small = { n: Int }
                data Large = { n: Int }
                data Kept = { n: Int }

                behavior split : (i: In) -> Small | Large
                    constructs Small, Large
                let split (i) = {
                    guard i.n >= 100 else Small { n = i.n }
                    Large { n = i.n }
                }

                behavior keep : (l: Large) -> Kept
                    constructs Kept
                let keep (l) = Kept { n = l.n }

                behavior run = split >-> keep
                """, "run");

        assertEquals("In", assertInstanceOf(BoundaryInput.Nominal.class, sig.ins().get(0)).name().name());
        // `Small` retired where `keep` did not accept it, and `Kept` is what the last stage answers.
        assertEquals(List.of("Kept", "Small"), memberNames(sig.out()));
    }

    private static List<String> memberNames(BoundaryOutput out) {
        List<String> names = new ArrayList<>();
        assertInstanceOf(BoundaryOutput.Cases.class, out).members().forEach(m -> names.add(m.name()));
        return names;
    }

    /**
     * A type the boundary does not admit builds no signature, and what says so is the obligation that
     * owns it. The runner used to reach a fallback arm for each of these and report a compiler defect
     * in a reader's vocabulary; none of them arrives there now, and this is why.
     */
    @Test
    void aTypeTheBoundaryDoesNotAdmitBuildsNoSignature() {
        assertRefused("(Int, Int)", "E1311");
        assertRefused("List<Option<Int>>", "E1313");
        assertRefused("Raw", "E1325");
        assertRefused("List<Raw>", "E1325");
        assertRefused("Map<Int, String>", "E1314");
    }

    /**
     * Each structural position owns admissibility of the subtree under it, so which rule reports is
     * decided by where the type stands and not by an order between passes. An optional in key
     * position is refused for standing where a key goes: told to write {@code Int} there instead, the
     * author would earn the key rule next, because the optional was never the reason there.
     */
    @Test
    void thePositionOwnsTheDiagnostic() {
        assertRefused("Map<Option<Int>, String>", "E1314");
        assertRefused("List<Option<Int>>", "E1313");
        assertRefused("Map<String, Option<Int>>", "E1313");
    }

    /**
     * Where more than one position is wrong, the one the walk reaches first is reported — the
     * parameters in order, then the answer, and within a type from the outside in.
     *
     * <p>This replaces a precedence between rules, and is not the same order. The passes this grew
     * out of were rule-major: every parameter and the answer were asked about tuples before any of
     * them was asked about optionals, so a behavior taking an optional and answering a tuple was
     * reported for the tuple. There is no such order left to state, because there are no longer
     * passes to order — a position is asked everything at once, and the next position is asked after
     * it.
     */
    @Test
    void whereTwoPositionsAreWrongTheOneWalkedFirstIsReported() {
        assertDeclarationRefused("(x: Option<Int>) -> (Int, Int)", "E1313");
        assertDeclarationRefused("(n: Int, x: Option<Int>) -> (Int, Int)", "E1313");
        // and the answer, where the parameters have nothing to say
        assertDeclarationRefused("(n: Int) -> (Int, Int)", "E1311");
    }

    /**
     * A module wrong in a way signatures decide and wrong in a way they do not: both are reported,
     * and the boundary's refusal is what a caller taking the first error is shown.
     *
     * <p>Which of a module's phases reports first is not this walk's to say. A phase reports when
     * its answer is worked out, and signatures are worked out early — so this pins what a reader
     * sees rather than stating a rule about it. It is here because moving where signatures are made
     * could have changed it: these are the same two, in the same order, as before any of it.
     */
    @Test
    void aBoundaryRefusalIsShownAndTheOtherMistakeIsReportedToo() {
        String source = """
                module demo

                behavior bad : (x: Option<Int>) -> Int
                let bad (x) = 0

                behavior two : (a: Int, b: Int) -> Int
                let two (a, b) = a

                behavior run = bad >-> two
                """;
        assertTrue(err(source).getMessage().contains("E1313"), err(source).getMessage());

        Compilation compilation = Compilation.ofDocuments(
                java.util.Map.of("demo.sou", source), java.util.Set.of(), ModulePath.EMPTY);
        compilation.answerEverything();
        List<String> codes = new ArrayList<>();
        compilation.db().allReports()
                .forEach(found -> codes.add(found.report().diagnostic().code().toString()));
        assertTrue(codes.contains("E1313"), codes.toString());
        assertTrue(codes.contains("E1702"), "the stage arity is still reported: " + codes);
    }

    /** The same of an output, which is refused by the same obligations from the other side. */
    @Test
    void anAnswerIsSubjectToTheSameObligations() {
        CompileException e = err("""
                module demo
                data Out = { n: Int }
                behavior f : (n: Int) -> Map<Int, Out>
                    constructs Out
                let f (n) = Map.fromList([ (n, Out { n = n }) ])
                """);
        assertTrue(e.getMessage().contains("E1314"), e.getMessage());
    }

    /** A declaration with no {@code let} is an injection target, whose signature is admitted like
     *  any other — so what a row here holds is the boundary and nothing about a body. */
    private static void assertDeclarationRefused(String signature, String code) {
        CompileException e = err("""
                module demo
                data Out = { n: Int }
                behavior f : %s
                """.formatted(signature));
        assertTrue(e.getMessage().contains(code), "expected " + code + ": " + e.getMessage());
    }

    private static void assertRefused(String type, String code) {
        CompileException e = err("""
                module demo
                data Out = { n: Int }
                behavior f : (x: %s) -> Out
                    constructs Out
                let f (x) = Out { n = 1 }
                """.formatted(type));
        assertTrue(e.getMessage().contains(code), "expected " + code + ": " + e.getMessage());
    }
}
