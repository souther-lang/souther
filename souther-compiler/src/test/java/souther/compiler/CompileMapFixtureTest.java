package souther.compiler;

import souther.compiler.diag.CompileException;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A {@code Map} in an {@code example} fixture is written as a list of key/value pairs — Elm's
 * {@code Dict.fromList} and F#'s {@code Map.ofList}, and the same list literal a {@code Set} field
 * already takes. Which of the two a list means is decided by the field's declared type, so a
 * {@code List} field keeps reading as a list.
 */
class CompileMapFixtureTest {

    @Test
    void aMapFieldTakesAListOfPairsOnBothSides() {
        Compiler.compile("""
                module demo

                data In = { names: List<String> }
                data Out = { counts: Map<String, Int> }

                behavior count : (i: In) -> Out constructs Out

                let count (i) = Out {
                    counts = List.fold((acc, n) -> Map.upsert(n, 1, c -> c + 1, acc), Map.empty(), i.names)
                }

                example count
                    | "repeats are counted" : (In { names = [ "a", "a", "b" ] })
                        -> Out { counts = [ ("a", 2), ("b", 1) ] }
                    | "no names, no counts" : (In { names = [] }) -> Out { counts = [] }
                """);
    }

    @Test
    void aMapFixtureIsAlsoAnInput() {
        Compiler.compile("""
                module demo

                data Stock = { onHand: Map<String, Int> }
                data Level = { n: Int }

                behavior lookUp : (s: Stock, sku: String) -> Level constructs Level

                let lookUp (s, sku) = Level { n = Map.get(sku, s.onHand) |> Option.withDefault(0) }

                example lookUp
                    | "a stocked sku" : (Stock { onHand = [ ("apple", 3) ] }, "apple") -> Level { n = 3 }
                    | "an unknown sku" : (Stock { onHand = [ ("apple", 3) ] }, "pear") -> Level { n = 0 }
                """);
    }

    @Test
    void aNewtypeKeyedMapTakesItsKeysAsWritten() {
        Compiler.compile("""
                module demo

                data Sku = String
                data Stock = { onHand: Map<Sku, Int> }
                data Level = { n: Int }

                behavior size : (s: Stock) -> Level constructs Level

                let size (s) = Level { n = Map.size(s.onHand) }

                example size
                    | "two skus" : (Stock { onHand = [ (Sku("apple"), 3), (Sku("pear"), 1) ] })
                        -> Level { n = 2 }
                """);
    }

    @Test
    void aListFieldStillReadsAsAList() {
        // The list literal is not turned into a map where a List is declared.
        Compiler.compile("""
                module demo

                data In = { ns: List<Int> }
                data Out = { n: Int }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out { n = List.length(i.ns) }

                example run
                    | "three" : (In { ns = [ 1, 2, 3 ] }) -> Out { n = 3 }
                """);
    }

    @Test
    void aMapEntryMustBeAPair() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data In = { counts: Map<String, Int> }
                data Out = { n: Int }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out { n = Map.size(i.counts) }

                example run
                    | "not pairs" : (In { counts = [ "a", "b" ] }) -> Out { n = 2 }
                """));
        assertTrue(e.getMessage().contains("(key, value)"), e.getMessage());
    }
}
