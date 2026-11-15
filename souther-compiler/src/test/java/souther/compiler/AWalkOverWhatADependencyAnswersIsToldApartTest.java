package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A rewrite of a walk over a list that only a dependency's answer holds is decided where a row
 * stands the dependency in with an answer of more elements than the module's table gives.
 *
 * <p>The table answers one element however it is asked, so no row run against it takes a second
 * step of the walk, and growing the inputs does not change that. What the walk goes over is what
 * the dependency answers, so that is what a candidate changes.
 */
class AWalkOverWhatADependencyAnswersIsToldApartTest {

    private static final String STOCK = """
            module repro.stock

            data Stock = { sku: String, qty: Int }

            behavior readStock : (sku: String) -> List<Stock>

            behavior available : (sku: String, want: Int) -> Bool
                depends on readStock

            let available (sku, want, readStock) =
                List.indexBy(.sku, readStock(sku))
                    |> Map.get(sku)
                    |> Option.map(s -> s.qty >= want)
                    |> Option.withDefault(false)

            fake readStock
                | _ -> [ Stock { sku = "apple", qty = 3 } ]

            example available
                | "enough" : ("apple", 2) -> true
                | "too many" : ("apple", 5) -> false
                | "unknown" : ("pear", 1) -> false
            """;

    @Test
    void aTableAnsweringOneElementDoesNotLeaveTheRewritesOpen() {
        WalkRewritesOwed.assertToldApart(measured(STOCK), "indexBy");
    }

    /**
     * What tells the rewrite apart is a value in the answer the table gives that no row asks
     * about as it stands: the elements are made of what the row holds, so the row that asks about
     * "plum" is stood a dependency answering "plum".
     */
    @Test
    void aTableAnsweringTwoElementsAndARowAskingForNeitherIsDecided() {
        String source = STOCK
                .replace("| _ -> [ Stock { sku = \"apple\", qty = 3 } ]",
                        "| _ -> [ Stock { sku = \"apple\", qty = 3 }, Stock { sku = \"pear\", qty = 1 } ]")
                .replace("| \"unknown\" : (\"pear\", 1) -> false",
                        "| \"unknown\" : (\"plum\", 1) -> false");

        WalkRewritesOwed.assertToldApart(measured(source), "indexBy");
    }

    /**
     * A list the input holds that the walk does not go over is not where a second step is looked
     * for: the date the schedule is read at is what the step compares, and it is moved before the
     * lists are grown.
     */
    @Test
    void aListTheWalkDoesNotGoOverIsNotGrownBeforeThePositionTheStepCompares() {
        String source = """
                module repro.schedule

                data Category = Standard | Reduced

                data Change = { from: Int, rate: Int }

                data Item = { name: String, qty: Int }

                behavior scheduleOf : (k: Category) -> List<Change>

                behavior rateOn : (k: Category, items: List<Item>, on: Int) -> Int
                    depends on scheduleOf

                let rateOn (k, items, on, scheduleOf) =
                    List.length(items) + (List.filter(c -> c.from <= on, scheduleOf(k))
                        |> List.reverse |> List.get(0) |> Option.map(.rate) |> Option.withDefault(0))

                fake scheduleOf
                    | (Standard) -> [ Change { from = 10, rate = 3 }, Change { from = 20, rate = 5 }, Change { from = 30, rate = 8 } ]
                    | (Reduced) -> [ Change { from = 30, rate = 4 } ]

                example rateOn
                    | "late" : (Standard, [ Item { name = "a", qty = 1 } ], 40) -> 9
                    | "before" : (Reduced, [ Item { name = "a", qty = 1 }, Item { name = "b", qty = 2 } ], 29) -> 2
                    | "none" : (Reduced, [ ], 29) -> 0
                """;

        WalkRewritesOwed.assertToldApart(measured(source), "filter");
    }

    /**
     * A walk over a list made of the input's, which the input does not hold as it is, is decided by
     * growing the input's list, though the positions are moved before the lists are grown.
     */
    @Test
    void aWalkOverAListMadeOfTheInputsIsDecidedByGrowingTheInputs() {
        String source = """
                module repro.derived

                data Item = { name: String, qty: Int }

                behavior total : (items: List<Item>, limit: Int) -> Int

                let total (items, limit) =
                    List.sum(List.map(i -> i.qty + limit, List.filter(i -> i.qty > 0, items)))

                example total
                    | "none" : ([ ], 5) -> 0
                    | "one" : ([ Item { name = "a", qty = 2 } ], 5) -> 7
                """;

        WalkRewritesOwed.assertToldApart(measured(source), "map");
    }

    /**
     * A walk over a list of the input is still decided where a dependency answers a list too: the
     * rows written hold no list of two, so the input's list has to be grown.
     */
    @Test
    void aWalkOverAnInputIsStillDecidedByTheInput() {
        String source = """
                module repro.inputs

                data Stock = { sku: String, qty: Int }

                behavior readTags : (sku: String) -> List<String>

                behavior total : (lines: List<Stock>, sku: String) -> Int
                    depends on readTags

                let total (lines, sku, readTags) =
                    List.length(readTags(sku)) + List.sum(List.map(l -> l.qty, lines))

                fake readTags
                    | _ -> [ "x" ]

                example total
                    | "none" : ([ ], "a") -> 1
                    | "one" : ([ Stock { sku = "a", qty = 2 } ], "a") -> 3
                """;

        WalkRewritesOwed.assertToldApart(measured(source), "map");
    }

    /**
     * An element of the answer is made of the values the row holds, as many of them as it has
     * leaves: the second key a lookup asks for is found in the answer as the first is.
     */
    @Test
    void anElementIsMadeOfMoreThanTheFirstValueTheRowHolds() {
        String source = """
                module repro.both

                data Stock = { sku: String, qty: Int }

                behavior readStock : (sku: String) -> List<Stock>

                behavior bothHeld : (sku: String, other: String) -> Bool
                    depends on readStock

                let bothHeld (sku, other, readStock) = {
                    let held = List.indexBy(.sku, readStock(sku))
                    Map.containsKey(other, held)
                }

                fake readStock
                    | _ -> [ Stock { sku = "apple", qty = 3 } ]

                example bothHeld
                    | "found" : ("a", "apple") -> true
                    | "absent" : ("a", "pear") -> false
                """;

        WalkRewritesOwed.assertToldApart(measured(source), "indexBy");
    }

    /**
     * What a dependency answers keeps its rows apart by a key a newtype wraps: two rows of one key
     * are refused, so an answer of two has two keys, and the values the row holds for them are the
     * strings inside the newtype.
     */
    @Test
    void aKeyWrappedInANewtypeIsMadeOfTheStringsTheRowHolds() {
        String source = """
                module repro.keyed

                data Sku = String

                data Line = { sku: Sku, quantity: Int }

                data Snapshot = { rows: List<Line> }
                    invariant List.allDistinctBy(.sku, rows)

                data Order = { sku: Sku, want: Int }

                behavior readStock : (order: Order) -> Snapshot

                behavior available : (order: Order) -> Bool
                    depends on readStock

                let available (order, readStock) =
                    List.indexBy(.sku, readStock(order).rows)
                        |> Map.get(order.sku)
                        |> Option.map(l -> l.quantity >= order.want)
                        |> Option.withDefault(false)

                fake readStock
                    | _ -> Snapshot { rows = [ Line { sku = Sku("apple"), quantity = 3 } ] }

                example available
                    | "enough" : (Order { sku = Sku("apple"), want = 2 }) -> true
                    | "too many" : (Order { sku = Sku("apple"), want = 5 }) -> false
                    | "unknown" : (Order { sku = Sku("pear"), want = 1 }) -> false
                """;

        WalkRewritesOwed.assertToldApart(measured(source), "indexBy");
    }

    /**
     * What a dependency answers has an invariant of its own that a longer list breaks: no answer
     * of two is one the type admits, so none is stood in, and the rewrites are left open as the
     * search that met a refusal leaves them. A row stood in with an answer the type refuses is
     * one nothing can run.
     */
    @Test
    void anAnswerTheTypeRefusesIsNotStoodIn() {
        String source = """
                module repro.snapshot

                data Stock = { sku: String, qty: Int }

                data Snapshot = { rows: List<Stock> }
                    invariant List.length(rows) <= 1

                behavior readStock : (sku: String) -> Snapshot

                behavior available : (sku: String, want: Int) -> Bool
                    depends on readStock

                let available (sku, want, readStock) =
                    List.indexBy(.sku, readStock(sku).rows)
                        |> Map.get(sku)
                        |> Option.map(s -> s.qty >= want)
                        |> Option.withDefault(false)

                fake readStock
                    | _ -> Snapshot { rows = [ Stock { sku = "apple", qty = 3 } ] }

                example available
                    | "enough" : ("apple", 2) -> true
                    | "too many" : ("apple", 5) -> false
                    | "unknown" : ("pear", 1) -> false
                """;

        Compilation compilation = measured(source);

        assertEquals(List.of("fold_after_one_step: undecided", "fold_from_the_seed: undecided"),
                WalkRewritesOwed.of(compilation, "indexBy"));
    }

    /**
     * A dependency the walk does not read can still be what lets a difference of the walk reach
     * the answer: the walk's result is only looked at where the other dependency answers enough
     * elements. What is stood in for it is asked after what the walk reads, and not left out.
     */
    @Test
    void aDependencyTheWalkDoesNotReadIsStoodInWhereItMasksTheWalk() {
        String source = """
                module repro.masked

                behavior stock : (k: Int) -> List<Int>

                behavior gate : (k: Int) -> List<Int>

                behavior check : (k: Int) -> Bool
                    depends on stock
                    depends on gate

                let check (k, stock, gate) =
                    List.length(List.filter(x -> x > 1, stock(k))) >= 2
                        && List.length(gate(k)) >= 2

                fake stock
                    | _ -> [ 0, 2, 2, 0 ]

                fake gate
                    | _ -> [ 0 ]

                example check
                    | "masked" : (0) -> false
                """;

        WalkRewritesOwed.assertToldApart(measured(source), "filter");
    }

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        return ACompiledModel.compiles(compilation);
    }
}
