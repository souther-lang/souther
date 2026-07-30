package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Severity;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The intraprocedural invariant-discharge check (spec §invariant-discharge): a construction whose
 * invariant the guards discharge is silent; one they leave possibly-violated is a warning (a possible
 * abort); one proven to violate on a reachable path is a compile error. Seeding an input's invariant
 * (a newtype's own bound, a product data's relation between fields) is what lets a guarded or reified
 * construction discharge.
 */
class CompileInvariantDischargeTest {

    private static long warnings(Compiler.Compiled c) {
        return c.warnings().stream().filter(d -> d.severity() == Severity.WARNING).count();
    }

    private static boolean hasWarning(Compiler.Compiled c, String code) {
        return c.warnings().stream()
                .anyMatch(d -> d.severity() == Severity.WARNING && code.equals(d.code()));
    }

    @Test
    void aConstructionProvenToViolateIsAnError() {
        // 0 - 1 = -1, which the non-negative invariant rejects — proven at compile time
        String m = """
                module demo
                data Money = Decimal
                    invariant value >= 0m
                behavior calc : (m: Money) -> Money constructs Money
                let calc (m) = Money(0m) - Money(1m)
                """;
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(m));
        assertEquals("E2010", e.diagnostic().code(),
                "a definite violation is E2010: " + e.getMessage());
    }

    @Test
    void aSumOfNonNegativesDischarges() {
        // a, b >= 0 (their own invariant) => a + b >= 0, so the re-wrap needs no guard — no warning
        String m = """
                module demo
                data Money = Decimal
                    invariant value >= 0m
                data Pair = { a: Money, b: Money }
                behavior total : (p: Pair) -> Money
                let total (p) = p.a + p.b
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)));
    }

    @Test
    void anUnguardedSubtractionIsAPossibleViolationWarning() {
        // a - b can go negative with no guard relating a and b — a possible abort, warned by default
        String m = """
                module demo
                data Money = Decimal
                    invariant value >= 0m
                data Pair = { a: Money, b: Money }
                behavior diff : (p: Pair) -> Money
                let diff (p) = p.a - p.b
                """;
        Compiler.Compiled c = Compiler.compileWithWarnings(m);
        assertFalse(c.classes().isEmpty(), "a warning does not fail the build");
        assertTrue(hasWarning(c, "E2011"), "an unguarded subtraction should warn (E2011)");
    }

    @Test
    void reifyingTheRelationAsAnInvariantDischarges() {
        // declaring `額 <= 残高` on the input data lets the subtraction discharge with no guard here
        String m = """
                module demo
                data Money = Decimal
                    invariant value >= 0m
                data 引落指示 = { 残高: Money, 額: Money }
                    invariant 額 <= 残高
                behavior 差引く : (指示: 引落指示) -> Money
                let 差引く (指示) = 指示.残高 - 指示.額
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "the reified relation discharges the subtraction");
    }

    @Test
    void aConstructionInsideAMapClosureIsAnalyzed() {
        // the closure element x: Money carries x >= 0; `x - Money(1m)` can go negative, so it is a
        // possible violation. Without binding the combinator's element parameter the construction
        // would be opaque (no diagnostic) — this pins that the closure body is analyzed.
        String m = """
                module demo
                data Money = Decimal
                    invariant value >= 0m
                data Bag = { items: List<Money> }
                behavior shift : (b: Bag) -> List<Money> constructs Money
                let shift (b) = List.map(x -> x - Money(1m), b.items)
                """;
        assertTrue(hasWarning(Compiler.compileWithWarnings(m), "E2011"),
                "a construction inside a map closure should be analyzed");
    }

    @Test
    void anUnguardedListLengthConstructionIsAPossibleViolationWarning() {
        // `List.length(xs)` is a term the domain can name, so an invariant over it is expressible and
        // the unguarded construction is flagged rather than left silent
        String m = """
                module demo
                data Lines = List<Int>
                    invariant List.length(value) >= 1
                behavior build : (xs: List<Int>) -> Lines constructs Lines
                let build (xs) = Lines(xs)
                """;
        assertTrue(hasWarning(Compiler.compileWithWarnings(m), "E2011"),
                "an unguarded length invariant should warn (E2011)");
    }

    @Test
    void aGuardOnTheLengthDischargesTheConstruction() {
        // the guard and the invariant name the same list, so they name the same atom
        String m = """
                module demo
                data NoItems
                data Lines = List<Int>
                    invariant List.length(value) >= 1
                behavior build : (xs: List<Int>) -> Lines | NoItems constructs Lines, NoItems
                let build (xs) = {
                    guard List.length(xs) >= 1
                        else NoItems
                    Lines(xs)
                }
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "the guard discharges the length invariant");
    }

    @Test
    void aGuardOnAnotherListDoesNotDischarge() {
        // the atom is keyed by the container the call names — guarding `ys` says nothing about `xs`
        String m = """
                module demo
                data NoItems
                data Lines = List<Int>
                    invariant List.length(value) >= 1
                behavior build : (xs: List<Int>, ys: List<Int>) -> Lines | NoItems
                    constructs Lines, NoItems
                let build (xs, ys) = {
                    guard List.length(ys) >= 1
                        else NoItems
                    Lines(xs)
                }
                """;
        assertTrue(hasWarning(Compiler.compileWithWarnings(m), "E2011"),
                "a guard on another list should not discharge");
    }

    @Test
    void aGuardOnAStringLengthDischargesTheConstruction() {
        String m = """
                module demo
                data TooShort
                data Name = String
                    invariant String.length(value) >= 3
                behavior build : (s: String) -> Name | TooShort constructs Name, TooShort
                let build (s) = {
                    guard String.length(s) >= 3
                        else TooShort
                    Name(s)
                }
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "the guard discharges the string-length invariant");
    }

    @Test
    void anUnguardedStringLengthConstructionIsAPossibleViolationWarning() {
        String m = """
                module demo
                data Name = String
                    invariant String.length(value) >= 3
                behavior build : (s: String) -> Name constructs Name
                let build (s) = Name(s)
                """;
        assertTrue(hasWarning(Compiler.compileWithWarnings(m), "E2011"),
                "an unguarded string-length invariant should warn (E2011)");
    }

    @Test
    void aGuardOnASetSizeDischargesTheConstruction() {
        String m = """
                module demo
                data Empty
                data Tags = Set<String>
                    invariant Set.size(value) >= 1
                behavior build : (s: Set<String>) -> Tags | Empty constructs Tags, Empty
                let build (s) = {
                    guard Set.size(s) >= 1
                        else Empty
                    Tags(s)
                }
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "the guard discharges the set-size invariant");
    }

    @Test
    void aGuardOnAMapSizeDischargesTheConstruction() {
        String m = """
                module demo
                data Empty
                data Index = Map<String, Int>
                    invariant Map.size(value) >= 1
                behavior build : (m: Map<String, Int>) -> Index | Empty constructs Index, Empty
                let build (m) = {
                    guard Map.size(m) >= 1
                        else Empty
                    Index(m)
                }
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "the guard discharges the map-size invariant");
    }

    @Test
    void anInputTypesLengthInvariantIsSeeded() {
        // `l: Lines` was built through Lines' checked construction, so its length is known here
        String m = """
                module demo
                data Lines = List<Int>
                    invariant List.length(value) >= 1
                data Batch = List<Int>
                    invariant List.length(value) >= 1
                behavior rewrap : (l: Lines) -> Batch constructs Batch
                let rewrap (l) = Batch(l.value)
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "the input newtype's length invariant discharges the re-wrap");
    }

    @Test
    void aLengthInvariantOverAMappedListStaysOpaque() {
        // `List.length(List.map(f, xs))` is not the same atom as `List.length(xs)` at this increment,
        // so the clause is not expressible here and the run-time check stands — no warning no guard
        // written over the mapped list could silence
        String m = """
                module demo
                data Lines = List<Int>
                    invariant List.length(value) >= 1
                behavior build : (xs: List<Int>) -> Lines constructs Lines
                let build (xs) = Lines(List.map(x -> x + 1, xs))
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "an unnameable container leaves the clause opaque");
    }

    @Test
    void aRebindingOfTheGuardedNameDropsTheFact() {
        // `xs` is rebound between the guard and the construction, so the guard's fact no longer holds
        // of what `Lines` is built from
        String m = """
                module demo
                data NoItems
                data Lines = List<Int>
                    invariant List.length(value) >= 1
                behavior build : (xs: List<Int>) -> Lines | NoItems constructs Lines, NoItems
                let build (xs) = {
                    guard List.length(xs) >= 1
                        else NoItems
                    let xs = List.filter(x -> x > 0, xs)
                    Lines(xs)
                }
                """;
        assertTrue(hasWarning(Compiler.compileWithWarnings(m), "E2011"),
                "a rebinding invalidates the guard's fact about that name");
    }

    @Test
    void aRequireGuardDischargesTheSubtraction() {
        // `guard 額 <= 残高` establishes the relation on the mainline, discharging `残高 - 額`
        String m = """
                module demo
                data Money = Decimal
                    invariant value >= 0m
                data 残高不足
                data 引落指示 = { 残高: Money, 額: Money }
                behavior 差引く : (指示: 引落指示) -> Money | 残高不足
                let 差引く (指示) = {
                    guard 指示.額 <= 指示.残高
                        else 残高不足
                    指示.残高 - 指示.額
                }
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "the guard discharges the subtraction");
    }
}
