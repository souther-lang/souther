package souther.compiler;

import souther.compiler.diag.Severity;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A construction's result is no smaller than a source it reads, and a lower-bound invariant is
 * discharged by that alone.
 *
 * <p>What the check could say about a size was how much of it a construction dropped: the same count
 * or fewer. An operation given two containers, or given one and an element to put in it, was left
 * saying nothing, because saying anything meant saying it about the elements — and there is no
 * element relation to a single source to state: {@code List.append(a, b)} holds {@code a}'s elements
 * and {@code b}'s and neither of them alone, and an insert puts in an element or an entry the
 * container it read did not hold. The bound on the count is not that statement and survived it, and
 * was discarded with it anyway.
 *
 * <p>So a non-empty list appended to a non-empty list was possibly empty, and the warning could not
 * be cleared: there is no relation between the two operands to reify, and guarding would ask the
 * author for a departure case for a failure that cannot happen.
 */
class CompileSizeNeverSmallerThanItsSourceTest {

    private static long warnings(Compiler.Compiled c) {
        return c.warnings().stream().filter(d -> d.severity() == Severity.WARNING).count();
    }

    private static boolean hasWarning(Compiler.Compiled c, String code) {
        return c.warnings().stream()
                .anyMatch(d -> d.severity() == Severity.WARNING && code.equals(d.code()));
    }

    private static final String NON_EMPTY = """
            data NEL = List<Int>
                invariant List.length(value) >= 1
            data NES = Set<Int>
                invariant Set.size(value) >= 1
            data NEM = Map<String, Int>
                invariant Map.size(value) >= 1
            """;

    private static String model(String body) {
        return "module demo\n" + NON_EMPTY + body;
    }

    // --- what the lower bound discharges ---------------------------------------------------------

    @Test
    void appendingToANonEmptyListStaysNonEmpty() {
        String m = model("""
                behavior both : (a: NEL, b: NEL) -> NEL
                let both (a, b) = NEL(List.append(a.value, b.value))
                """);
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "length(a) >= 1 and the result is no shorter than a");
    }

    /** The second operand is as much a lower bound as the first: what is appended to what is the
     * author's order, not the check's. */
    @Test
    void appendingANonEmptyListOnTheRightStaysNonEmpty() {
        String m = model("""
                behavior right : (a: List<Int>, b: NEL) -> NEL
                let right (a, b) = NEL(List.append(a, b.value))
                """);
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)));
    }

    @Test
    void insertingIntoANonEmptySetKeepsItNonEmpty() {
        String m = model("""
                behavior add : (s: NES, x: Int) -> NES
                let add (s, x) = NES(Set.insert(x, s.value))
                """);
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)));
    }

    @Test
    void insertingIntoANonEmptyMapKeepsItNonEmpty() {
        String m = model("""
                behavior put : (m: NEM, k: String, v: Int) -> NEM
                let put (m, k, v) = NEM(Map.insert(k, v, m.value))
                """);
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)));
    }

    @Test
    void aUnionWithANonEmptySetIsNonEmpty() {
        String m = model("""
                behavior joined : (a: NES, b: Set<Int>) -> NES
                let joined (a, b) = NES(Set.union(a.value, b))
                """);
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)));
    }

    @Test
    void aUnionWithANonEmptyMapIsNonEmpty() {
        String m = model("""
                behavior merged : (a: Map<String, Int>, b: NEM) -> NEM
                let merged (a, b) = NEM(Map.union(a, b.value))
                """);
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)));
    }

    // --- the operator spelling ---------------------------------------------------------------------

    /** {@code List.append} is written {@code a ++ b} in the library it is declared in, so the two are
     * one operation and the rule is about both. */
    @Test
    void concatenatingNonEmptyListsStaysNonEmpty() {
        String m = model("""
                behavior joined : (a: NEL, b: NEL) -> NEL
                let joined (a, b) = NEL(a.value ++ b.value)
                """);
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)));
    }

    /** A string has no {@code append} to be the other spelling of, so the operator is the only way
     * this is written and the only place the rule can reach it. */
    @Test
    void concatenatingNonEmptyStringsStaysNonEmpty() {
        String m = """
                module demo
                data S = String
                    invariant String.length(value) >= 1
                behavior joined : (a: S, b: S) -> S
                let joined (a, b) = S(a.value ++ b.value)
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)));
    }

    @Test
    void concatenatingWithANonEmptyStringOnEitherSideIsEnough() {
        String m = """
                module demo
                data S = String
                    invariant String.length(value) >= 1
                behavior prefixed : (a: String, b: S) -> S
                let prefixed (a, b) = S(a ++ b.value)
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)));
    }

    // --- what it must not discharge ---------------------------------------------------------------

    @Test
    void concatenatingTwoStringsThatMayBeEmptyIsStillUnproven() {
        String m = """
                module demo
                data S = String
                    invariant String.length(value) >= 1
                behavior joined : (a: String, b: String) -> S
                let joined (a, b) = S(a ++ b)
                """;
        assertTrue(hasWarning(Compiler.compileWithWarnings(m), "E2011"));
    }

    @Test
    void anUpperBoundIsNotDischargedByAConcatenation() {
        String m = """
                module demo
                data Short = String
                    invariant String.length(value) <= 10
                behavior joined : (a: Short, b: Short) -> Short
                let joined (a, b) = Short(a.value ++ b.value)
                """;
        assertTrue(hasWarning(Compiler.compileWithWarnings(m), "E2011"),
                "two short strings concatenate to a long one");
    }


    /** Nothing here is known to hold anything, so the result is not known to either. */
    @Test
    void appendingTwoListsThatMayBeEmptyIsStillUnproven() {
        String m = model("""
                behavior maybe : (a: List<Int>, b: List<Int>) -> NEL
                let maybe (a, b) = NEL(List.append(a, b))
                """);
        assertTrue(hasWarning(Compiler.compileWithWarnings(m), "E2011"),
                "two possibly-empty lists append to a possibly-empty list");
    }

    /**
     * The direction is the whole of the rule. A bound from below says nothing about a bound from
     * above, and appending is where the two part company: two lists of at most ten make a list of up
     * to twenty. A rule written the other way round would discharge this and admit an abort.
     */
    @Test
    void anUpperBoundIsNotDischargedByALowerBound() {
        String m = """
                module demo
                data Small = List<Int>
                    invariant List.length(value) <= 10
                behavior grow : (a: Small, b: Small) -> Small
                let grow (a, b) = Small(List.append(a.value, b.value))
                """;
        assertTrue(hasWarning(Compiler.compileWithWarnings(m), "E2011"),
                "appending two short lists can make a long one");
    }

    /** Inserting adds at most one, so what an upper bound allowed before it is not what it allows
     * after. */
    @Test
    void anUpperBoundIsNotDischargedByAnInsert() {
        String m = """
                module demo
                data Small = Set<Int>
                    invariant Set.size(value) <= 10
                behavior add : (s: Small, x: Int) -> Small
                let add (s, x) = Small(Set.insert(x, s.value))
                """;
        assertTrue(hasWarning(Compiler.compileWithWarnings(m), "E2011"));
    }
}
