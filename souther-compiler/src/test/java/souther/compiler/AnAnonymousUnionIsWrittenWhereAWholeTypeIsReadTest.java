package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.CompileException;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Where {@code A | B} is read as a type, and which of those positions take it, held against the
 * compiler rather than against a sentence.
 *
 * <p>Two rules decide it between them and neither owns the other's half. Which positions read a whole
 * type is the grammar's answer ({@code a-type-is-written-in-a-type-position}); what a behavior's
 * boundary admits is the representation's ({@code a-parameter-names-one-type}). Read together they
 * say the form is read wherever a whole type is read and admitted by every one of those positions but
 * one, which is not the claim five sentences used to make — that it appears only in a behavior's
 * output.
 *
 * <p>Held here because prose cannot be run. The document said the narrower thing in five places for
 * as long as nothing measured it, and each of those places was true of the boundary and false of a
 * signature.
 */
class AnAnonymousUnionIsWrittenWhereAWholeTypeIsReadTest {

    /** The declarations every case is written against. */
    private static final String TYPES = """
            module p exposing (A, B, C, Out, run)

            data A = { a: Int }
            data B = { b: Int }
            data C = { c: Int }
            data Out = { v: Int }
            """;

    /** A behavior, so that a module which is only exercising a position still has one. */
    private static final String BEHAVIOR = """
            behavior run : (i: Out) -> Out
                constructs Out

            let run (i) = Out { v = 1 }
            """;

    /** The code a source is refused with, or "ok" where it compiles. */
    private static String verdict(String written) {
        try {
            Compiler.compile(TYPES + "\n" + written + "\n" + BEHAVIOR);
            return "ok";
        } catch (CompileException e) {
            return e.diagnostic().code();
        }
    }

    private static Map<String, String> verdicts(Map<String, String> positions) {
        Map<String, String> out = new LinkedHashMap<>();
        positions.forEach((position, written) -> out.put(position, verdict(written)));
        return out;
    }

    /**
     * Every position a whole type is read in takes one, except the one the boundary refuses.
     *
     * <p>That exception is a behavior's parameter and it is held below, so what this holds is the
     * rest: the positions no representation rule reaches. Asked as one map rather than one test each,
     * because what is being held is that the set matches — a position dropping out of it is the
     * defect, and a test per position reports that as one failure beside several passes.
     */
    @Test
    void everyNonBoundaryWholeTypePositionTakesOne() {
        Map<String, String> positions = new LinkedHashMap<>();
        positions.put("helper parameter", "let f (x: A | B) : Int = 1");
        positions.put("helper declared return", "let f (n: Int) : A | B = A { a = n }");
        positions.put("local binding annotation", """
                let f (n: Int) : Int = {
                    let z: A | B = A { a = 1 }
                    1
                }""");
        positions.put("function type parameter", "let f (g: (A | B) -> Int) : Int = 1");
        positions.put("function type result", "let f (g: (Int) -> A | B) : Int = 1");

        Map<String, String> expected = new LinkedHashMap<>(positions);
        expected.replaceAll((_, _) -> "ok");
        assertEquals(expected, verdicts(positions));
    }

    /** A behavior's output is one of those, and it is the position the form is for. */
    @Test
    void aBehaviorsOutputTakesOne() {
        assertEquals("ok", verdictOfWholeModule("""
                module p exposing (A, B, run)

                data A = { a: Int }
                data B = { b: Int }

                behavior run : (n: Int) -> A | B
                    constructs A

                let run (n) = A { a = n }
                """));
    }

    /**
     * The positions that refuse one, and what each refuses it for.
     *
     * <p>The three that are a syntax error are not a rule about unions: the grammar reads no whole
     * type there, which is the same reason {@code List<T?>} is not written either. One position
     * refuses a union it could have read, and that one is the boundary.
     */
    @Test
    void thePositionsThatRefuseOneSayWhichRefusalItIs() {
        Map<String, String> positions = new LinkedHashMap<>();
        positions.put("data field", "data Holder = { u: A | B }");
        positions.put("type argument", "let f (xs: List<A | B>) : Int = 1");
        positions.put("tuple member", "let f (t: (A | B, Int)) : Int = 1");

        Map<String, String> expected = new LinkedHashMap<>(positions);
        expected.replaceAll((_, _) -> "E2301");
        assertEquals(expected, verdicts(positions),
                "no whole type is read there, so the grammar refuses the form");
        assertEquals("E1312", verdictOfWholeModule("""
                module p exposing (A, B, Out, run)

                data A = { a: Int }
                data B = { b: Int }
                data Out = { v: Int }

                behavior run : (i: A | B) -> Out
                    constructs Out

                let run (i) = Out { v = 1 }
                """), "and the boundary refuses one it could have read");
    }

    /**
     * A union in a signature is a type and not a form that was let through.
     *
     * <p>Which is what settles whether the narrower sentence could be made true by adding a
     * diagnostic. The members are known, a {@code match} over them is checked in both directions, and
     * an argument is held to them — so refusing one in a signature would take a working type away
     * rather than close a hole.
     */
    @Test
    void aUnionInASignatureIsCheckedLikeAnyOtherType() {
        Map<String, String> written = new LinkedHashMap<>();
        written.put("a match missing a member", """
                let f (x: A | B) : Int =
                    match x with
                        | A as u -> u.a""");
        written.put("a match arm for a non-member", """
                let f (x: A | B) : Int =
                    match x with
                        | A as u -> u.a
                        | B as u -> u.b
                        | C as u -> u.c""");
        written.put("a non-member handed to it", """
                let f (x: A | B) : Int = 1

                let g (n: Int) : Int = f(C { c = 1 })""");

        Map<String, String> expected = new LinkedHashMap<>();
        expected.put("a match missing a member", "E1201");
        expected.put("a match arm for a non-member", "E1203");
        expected.put("a non-member handed to it", "E1317");
        assertEquals(expected, verdicts(written));
    }

    private static String verdictOfWholeModule(String source) {
        try {
            Compiler.compile(source);
            return "ok";
        } catch (CompileException e) {
            return e.diagnostic().code();
        }
    }
}
