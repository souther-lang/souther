package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A collection reaches an {@code example} in every position a value does: as a behavior's argument,
 * as its expected output, and as a fake's value. The fixture forms are the ones a collection field
 * already takes — a list literal for a {@code List} or {@code Set}, a list of pairs for a
 * {@code Map} — so a behavior taking a `List` needs no wrapper data to be exampled (issue #97).
 */
class CompileExampleCollectionTest {

    @Test
    void aListArgumentIsExampled() {
        Compiler.compile("""
                module demo
                data Line = { qty: Int }
                data Total = { n: Int }

                behavior count : (lines: List<Line>) -> Total
                    constructs Total
                let count (lines) = Total { n = List.length(lines) }

                example count
                    | "two lines" : ([ Line { qty = 1 }, Line { qty = 2 } ]) -> Total { n = 2 }
                    | "none" : ([]) -> Total { n = 0 }
                """);
    }

    @Test
    void aSetArgumentDeduplicatesLikeASetField() {
        Compiler.compile("""
                module demo
                data Total = { n: Int }

                behavior count : (xs: Set<Int>) -> Total
                    constructs Total
                let count (xs) = Total { n = Set.size(xs) }

                example count
                    | "a repeat is one element" : ([ 1, 2, 2 ]) -> Total { n = 2 }
                """);
    }

    @Test
    void aMapArgumentIsWrittenAsPairs() {
        Compiler.compile("""
                module demo
                data Level = { n: Int }

                behavior lookUp : (stock: Map<String, Int>, sku: String) -> Level
                    constructs Level
                let lookUp (stock, sku) = Level { n = Map.get(sku, stock) |> Option.withDefault(0) }

                example lookUp
                    | "a stocked sku" : ([ ("apple", 3) ], "apple") -> Level { n = 3 }
                    | "an unknown sku" : ([ ("apple", 3) ], "pear") -> Level { n = 0 }
                """);
    }

    @Test
    void aNewtypeKeyedMapArgumentTakesItsKeysAsWritten() {
        Compiler.compile("""
                module demo
                data Sku = String
                data Level = { n: Int }

                behavior count : (stock: Map<Sku, Int>) -> Level
                    constructs Level
                let count (stock) = Level { n = Map.size(stock) }

                example count
                    | "two skus" : ([ (Sku("apple"), 3), (Sku("pear"), 1) ]) -> Level { n = 2 }
                """);
    }

    @Test
    void aNewtypeKeyedMapArgumentRunsTheKeysInvariant() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                data Sku = String
                    invariant String.length(value) > 0
                data Level = { n: Int }

                behavior count : (stock: Map<Sku, Int>) -> Level
                    constructs Level
                let count (stock) = Level { n = Map.size(stock) }

                example count
                    | "an empty sku" : ([ (Sku(""), 3) ]) -> Level { n = 1 }
                """));
        assertEquals("E1903", e.code(), e.getMessage());
    }

    @Test
    void everyBadKeyOfANewtypeKeyedMapIsReported() {
        // the derived decoder's rekey helper merges the failures of every key; the one built here
        // does the same, so a fixture with two bad keys names both
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                data Sku = String
                    invariant String.matches("[A-Z]-[0-9]+", value)
                data Level = { n: Int }

                behavior count : (stock: Map<Sku, Int>) -> Level
                    constructs Level
                let count (stock) = Level { n = Map.size(stock) }

                example count
                    | "two bad keys" : ([ (Sku("a"), 1), (Sku("b"), 2) ]) -> Level { n = 2 }
                """));
        assertEquals("E1903", e.code(), e.getMessage());
        assertTrue(e.getMessage().contains("a: ") && e.getMessage().contains("b: "),
                "both keys are reported, each named: " + e.getMessage());
    }

    @Test
    void aNestedCollectionArgumentIsExampled() {
        Compiler.compile("""
                module demo
                data Total = { n: Int }

                behavior count : (byDay: Map<String, List<Int>>) -> Total
                    constructs Total
                let count (byDay) = Total {
                    n = Map.fold((acc, day, ns) -> acc + List.length(ns), 0, byDay)
                }

                example count
                    | "two days" : ([ ("mon", [ 1, 2 ]), ("tue", [ 3 ]) ]) -> Total { n = 3 }
                """);
    }

    @Test
    void aCollectionOutputIsComparedAsAValue() {
        Compiler.compile("""
                module demo
                data Line = { qty: Int }

                behavior spread : (n: Int) -> List<Line>
                    constructs Line
                let spread (n) = [ Line { qty = n }, Line { qty = n } ]

                example spread
                    | "two of the same" : (3) -> [ Line { qty = 3 }, Line { qty = 3 } ]
                """);
    }

    @Test
    void aWrongCollectionOutputIsReported() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                data Line = { qty: Int }

                behavior spread : (n: Int) -> List<Line>
                    constructs Line
                let spread (n) = [ Line { qty = n }, Line { qty = n } ]

                example spread
                    | "one, not two" : (3) -> [ Line { qty = 3 } ]
                """));
        assertEquals("E1905", e.code(), e.getMessage());
        // both sides read in the notation the fixture is written in, elements named
        assertTrue(e.getMessage().contains("expected [ Line { qty = 3 } ]"), e.getMessage());
        assertTrue(e.getMessage().contains("but was [ Line { qty = 3 }, Line { qty = 3 } ]"),
                e.getMessage());
    }

    @Test
    void aCollectionValuedFakeIsBuilt() {
        Compiler.compile("""
                module demo
                data Line = { qty: Int }
                data Total = { n: Int }

                behavior fetch : (n: Int) -> List<Line>

                behavior count : (n: Int) -> Total
                    depends on fetch
                    constructs Total
                let count (n, fetch) = Total { n = List.length(fetch(n)) }

                example count
                    | "one line" : (1) with fetch = [ Line { qty = 1 } ] -> Total { n = 1 }
                """);
    }

    @Test
    void aCollectionFakeTableMatchesOnACollectionInput() {
        Compiler.compile("""
                module demo
                data Total = { n: Int }

                behavior sum : (ns: List<Int>) -> Total

                behavior report : (ns: List<Int>) -> Total
                    depends on sum
                let report (ns, sum) = sum(ns)

                fake sum
                  | ([ 1, 2 ]) -> Total { n = 3 }
                  | _ -> Total { n = 0 }

                example report
                    | "the listed row" : ([ 1, 2 ]) -> Total { n = 3 }
                    | "the default row" : ([ 9 ]) -> Total { n = 0 }
                """);
    }

    @Test
    void aListFixtureOfTheWrongShapeIsAFixtureError() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                data Line = { qty: Int }
                data Total = { n: Int }

                behavior count : (lines: List<Line>) -> Total
                    constructs Total
                let count (lines) = Total { n = List.length(lines) }

                example count
                    | "a string is not a line" : ([ "x" ]) -> Total { n = 1 }
                """));
        assertEquals("E1903", e.code(), e.getMessage());
        assertTrue(e.getMessage().contains("count"), e.getMessage());
    }
}
