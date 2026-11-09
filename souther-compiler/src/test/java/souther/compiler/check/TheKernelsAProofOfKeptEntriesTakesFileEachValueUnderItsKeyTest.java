package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.WhatTheLibraryComputes;
import souther.compiler.proof.AppliedClosures;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a proof of the entries a body keeps takes of the kernels it is written with is more than
 * which values they hold: that {@code Map.insert} files its value under its key and leaves every
 * other key's value as it was, that {@code Map.toList} lists each key with the value filed under
 * it and each once, that {@code Map.get} answers the value filed under the key, and that
 * {@code List.get} answers the element at the place. A kernel that kept the right values under the
 * wrong keys would hold every statement about which values and how many, and answer none of these.
 *
 * <p>Run over a table of maps and lists, each against operations written beside it that get it
 * wrong — one that overwrites values and, where the values are what is in question, one that keeps
 * every key and every value and files them under each other's keys — so what is held is held by a
 * check that can fail: the same check is found false of each of them.
 */
class TheKernelsAProofOfKeptEntriesTakesFileEachValueUnderItsKeyTest {

    private static final ValueName MAP_INSERT = ValueName.Stdlib.operation("Map", "insert");
    private static final ValueName MAP_TO_LIST = ValueName.Stdlib.operation("Map", "toList");
    private static final ValueName MAP_GET = ValueName.Stdlib.operation("Map", "get");
    private static final ValueName LIST_GET = ValueName.Stdlib.operation("List", "get");

    /** Each check is a behavior over one input. {@code wrong} is which operation it is run over:
     *  0 the library's, and each other number one written to get it wrong. */
    private static final String PROGRAM = """
            module demo

            data In = { m: Map<String, Int>, k: String, other: String, v: Int,
                        xs: List<Int>, i: Int, wrong: Int }
            data Out = { holds: Bool }

            behavior insertFilesUnderItsKeyAndLeavesTheRest : (in: In) -> Out
            let insertFilesUnderItsKeyAndLeavesTheRest (in) = {
                let real = Map.insert(in.k, in.v, in.m)
                let listed = Map.toList(real)
                let values = List.reverse(List.map(kv -> {
                    let (k2, v2) = kv
                    v2
                }, listed))
                let made = if in.wrong == 1
                    then Map.fromList(List.map(kv -> {
                        let (k2, v2) = kv
                        (k2, in.v)
                    }, listed))
                    else if in.wrong == 2
                    then Map.fromList(List.mapIndexed((at, kv) -> {
                        let (k2, v2) = kv
                        (k2, match List.get(at, values) with
                            | Some x -> x
                            | None -> 0)
                    }, listed))
                    else real
                let filed = match Map.get(in.k, made) with
                    | Some x -> x == in.v
                    | None -> false
                let kept = List.all(kv -> {
                    let (k2, v2) = kv
                    k2 == in.k || (match Map.get(k2, made) with
                        | Some x -> x == v2
                        | None -> false)
                }, Map.toList(in.m))
                Out { holds = filed && kept }
            }

            behavior toListPairsEachKeyWithItsValueOnce : (in: In) -> Out
            let toListPairsEachKeyWithItsValueOnce (in) = {
                let real = Map.toList(in.m)
                let values = List.reverse(List.map(kv -> {
                    let (k2, v2) = kv
                    v2
                }, real))
                let listed = if in.wrong == 1
                    then List.map(kv -> {
                        let (k2, v2) = kv
                        (k2, in.v)
                    }, real)
                    else if in.wrong == 2
                    then List.mapIndexed((at, kv) -> {
                        let (k2, v2) = kv
                        (k2, match List.get(at, values) with
                            | Some x -> x
                            | None -> 0)
                    }, real)
                    else real
                Out { holds = Map.fromList(listed) == in.m
                    && List.length(listed) == Map.size(in.m) }
            }

            behavior getAnswersTheValueFiledUnderTheKey : (in: In) -> Out
            let getAnswersTheValueFiledUnderTheKey (in) = {
                let found = if in.wrong == 1 then Map.get(in.other, in.m) else Map.get(in.k, in.m)
                Out { holds = match found with
                    | Some x -> List.any(kv -> {
                        let (k2, v2) = kv
                        k2 == in.k && v2 == x
                    }, Map.toList(in.m))
                    | None -> List.all(kv -> {
                        let (k2, v2) = kv
                        k2 /= in.k
                    }, Map.toList(in.m)) }
            }

            behavior listGetAnswersTheElementAtThePlace : (in: In) -> Out
            let listGetAnswersTheElementAtThePlace (in) = {
                let found = if in.wrong == 1 then List.get(in.i + 1, in.xs)
                    else List.get(in.i, in.xs)
                let expected = List.min(List.take(1, List.drop(in.i, in.xs)))
                Out { holds = match found with
                    | Some x -> in.i >= 0 && (match expected with
                        | Some y -> x == y
                        | None -> false)
                    | None -> in.i < 0 || (match expected with
                        | Some y -> false
                        | None -> true) }
            }
            """;

    /** What each of the four is declared to be, so what is run below is what is declared. */
    @Test
    void whatIsRunBelowIsWhatTheLibraryDeclares() {
        BoundOperationFacts facts = DefaultBoundOperationFacts.get();

        BoundOperationFact.PutsAValueIn put = facts.putsAValueIn(MAP_INSERT);
        assertNotNull(put);
        assertTrue(put.under().isPresent(), "an insert is declared to file under a key");
        assertInstanceOf(AppliedClosures.Listing.EveryEntryOf.class,
                Combinators.listing(DefaultStdlib.get(), facts,
                        (ValueName.Stdlib.Operation) MAP_TO_LIST),
                "a map's list is declared to list its entries");
        assertNotNull(facts.looksUp(MAP_GET));
        assertNotNull(facts.elementAt(LIST_GET));
    }

    /** What a check is run over: maps told apart by which key holds which value, keys present
     *  and absent, values, lists and places. A dimension a check is not about holds one value. */
    private record Table(List<Map<String, Long>> maps, List<String> keys, List<Long> values,
                         List<List<Long>> lists, List<Long> places) {

        static Table ofMaps(List<String> keys, List<Long> values) {
            return new Table(someMaps(), keys, values, List.of(List.of()), List.of(0L));
        }

        static Table ofLists() {
            return new Table(List.of(new LinkedHashMap<>()), List.of("a"), List.of(10L), someLists(),
                    List.of(-1L, 0L, 1L, 2L, 5L));
        }
    }

    @Test
    void aMapInsertFilesItsValueUnderItsKeyAndLeavesEveryOtherKeyAsItWas() throws Exception {
        runOver("insertFilesUnderItsKeyAndLeavesTheRest",
                Table.ofMaps(List.of("a", "b", "d"), List.of(10L, 20L, 30L)), 2);
    }

    @Test
    void aMapsListHasEachEntryOnceAsItsKeyWithItsValue() throws Exception {
        runOver("toListPairsEachKeyWithItsValueOnce",
                Table.ofMaps(List.of("a"), List.of(10L, 30L)), 2);
    }

    @Test
    void aMapGetAnswersTheValueFiledUnderItsKey() throws Exception {
        runOver("getAnswersTheValueFiledUnderTheKey",
                Table.ofMaps(List.of("a", "b", "d"), List.of(10L)), 1);
    }

    @Test
    void aListGetAnswersTheElementAtItsPlace() throws Exception {
        runOver("listGetAnswersTheElementAtThePlace", Table.ofLists(), 1);
    }

    /** The behavior {@code name} is true of every input as the library answers it, and false of
     *  some input for each of the {@code wrongOnes} operations written to get it wrong. */
    private static void runOver(String name, Table table, int wrongOnes) throws Exception {
        WhatTheLibraryComputes.Program program = new WhatTheLibraryComputes.Program("demo",
                PROGRAM);
        List<String> brokenByTheLibrary = new ArrayList<>();
        int[] caught = new int[wrongOnes + 1];
        for (Map<String, Long> map : table.maps()) {
            for (String key : table.keys()) {
                for (long value : table.values()) {
                    for (List<Long> list : table.lists()) {
                        for (long place : table.places()) {
                            for (int wrong = 0; wrong <= wrongOnes; wrong++) {
                                boolean holds = holds(program, name, map, key, value, list,
                                        place, wrong);
                                if (wrong == 0 && !holds) {
                                    brokenByTheLibrary.add(name + " " + map + " " + key + " "
                                            + value + " " + list + " " + place);
                                } else if (wrong > 0 && !holds) {
                                    caught[wrong]++;
                                }
                            }
                        }
                    }
                }
            }
        }
        assertEquals(List.of(), brokenByTheLibrary, "a kernel answering what the check says");
        for (int wrong = 1; wrong <= wrongOnes; wrong++) {
            assertTrue(caught[wrong] > 0, "the check is found false of the operation that gets"
                    + " it wrong in way " + wrong + ", or it holds nothing");
        }
    }

    private static boolean holds(WhatTheLibraryComputes.Program program, String name,
                                 Map<String, Long> map, String key, long value, List<Long> list,
                                 long place, int wrong) throws Exception {
        Map<String, Object> input = new LinkedHashMap<>();
        input.put("m", map);
        input.put("k", key);
        input.put("other", key.equals("a") ? "b" : "a");
        input.put("v", value);
        input.put("xs", list);
        input.put("i", place);
        input.put("wrong", (long) wrong);
        Map<?, ?> out = (Map<?, ?>) program.answer(name, "In", "Out", input);
        return Boolean.TRUE.equals(out.get("holds"));
    }

    /** Maps over a few keys, told apart by which key holds which of two values: one pair of them
     *  holds the same values under the keys the other way round. */
    private static List<Map<String, Long>> someMaps() {
        List<Map<String, Long>> out = new ArrayList<>();
        out.add(new LinkedHashMap<>());
        out.add(new LinkedHashMap<>(Map.of("a", 10L)));
        out.add(new LinkedHashMap<>(Map.of("a", 20L)));
        Map<String, Long> two = new LinkedHashMap<>();
        two.put("a", 10L);
        two.put("b", 20L);
        out.add(two);
        Map<String, Long> swapped = new LinkedHashMap<>();
        swapped.put("a", 20L);
        swapped.put("b", 10L);
        out.add(swapped);
        Map<String, Long> three = new LinkedHashMap<>();
        three.put("a", 10L);
        three.put("b", 20L);
        three.put("c", 10L);
        out.add(three);
        return out;
    }

    private static List<List<Long>> someLists() {
        return List.of(List.of(), List.of(7L), List.of(7L, 8L, 9L));
    }
}
