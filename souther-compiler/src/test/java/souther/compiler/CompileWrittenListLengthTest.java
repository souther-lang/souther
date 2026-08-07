package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Severity;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A list written out has as many elements as it is written with, whatever they are.
 *
 * <p>The count was asked through the question of whether the whole value was written — every element
 * a literal, and so on down — which is what naming a written value at a construction site needs and
 * is not what counting needs. So a three-element list built from three parameters was a list of
 * unknown length, and an invariant asking for two of them was left to the run-time check with no
 * guard an author could write to discharge it: the elements are the arguments, and the length is on
 * the line.
 */
class CompileWrittenListLengthTest {

    private static long warnings(Compiler.Compiled c) {
        return c.warnings().stream().filter(d -> d.severity() == Severity.WARNING).count();
    }

    private static boolean hasWarning(Compiler.Compiled c, String code) {
        return c.warnings().stream()
                .anyMatch(d -> d.severity() == Severity.WARNING && code.equals(d.code()));
    }

    @Test
    void aNewtypeOverAWrittenListIsAsLongAsItIsWritten() {
        String m = """
                module demo
                data P = { n: Int }
                data Entry = List<P>
                    invariant List.length(value) >= 2
                behavior make : (a: Int, b: Int, c: Int) -> Entry
                    constructs Entry, P
                let make (a, b, c) = Entry([ P { n = a }, P { n = b }, P { n = c } ])
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "three elements are written on the line, whatever they hold");
    }

    @Test
    void aRecordFieldGivenAWrittenListIsAsLongAsItIsWritten() {
        String m = """
                module demo
                data P = { n: Int }
                data Entry = { ps: List<P> }
                    invariant List.length(ps) >= 2
                behavior make : (a: Int, b: Int, c: Int) -> Entry
                    constructs Entry, P
                let make (a, b, c) = Entry { ps = [ P { n = a }, P { n = b }, P { n = c } ] }
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)));
    }

    /** The list is written where the name is, so naming it changes nothing about how long it is. */
    @Test
    void aNameGivenAWrittenListIsAsLongAsTheListItWasGiven() {
        String m = """
                module demo
                data P = { n: Int }
                data Entry = List<P>
                    invariant List.length(value) >= 2
                behavior make : (a: Int, b: Int) -> Entry
                    constructs Entry, P
                let make (a, b) = {
                    let ps = [ P { n = a }, P { n = b } ]
                    Entry(ps)
                }
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)));
    }

    // --- what it must not discharge ---------------------------------------------------------------

    /** A count read is a count the check decides with. Written too short, the invariant is refuted
     * rather than left unproven. */
    @Test
    void aListWrittenShorterThanTheInvariantNeedsIsAViolation() {
        String m = """
                module demo
                data P = { n: Int }
                data Entry = List<P>
                    invariant List.length(value) >= 2
                behavior make : (a: Int) -> Entry
                    constructs Entry, P
                let make (a) = Entry([ P { n = a } ])
                """;
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(m));
        assertEquals("E2010", e.diagnostic().code(), e.getMessage());
    }

    /** A list handed in was not written here, and how long it is is not on any line. */
    @Test
    void aListGivenAsAnInputIsStillUnproven() {
        String m = """
                module demo
                data P = { n: Int }
                data Entry = List<P>
                    invariant List.length(value) >= 2
                behavior make : (ps: List<P>) -> Entry
                    constructs Entry
                let make (ps) = Entry(ps)
                """;
        assertTrue(hasWarning(Compiler.compileWithWarnings(m), "E2011"));
    }
}
