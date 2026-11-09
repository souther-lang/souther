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
import static org.junit.jupiter.api.Assertions.assertFalse;
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
 * <p>Run over a table of maps and lists, each against an operation written beside it that gets it
 * wrong in the one way that matters, so what is held is held by a check that can fail: the same
 * check is found false of the wrong one.
 */
class TheKernelsAProofOfKeptEntriesTakesFileEachValueUnderItsKeyTest {

    private static final ValueName MAP_INSERT = ValueName.Stdlib.operation("Map", "insert");
    private static final ValueName MAP_TO_LIST = ValueName.Stdlib.operation("Map", "toList");
    private static final ValueName MAP_GET = ValueName.Stdlib.operation("Map", "get");
    private static final ValueName LIST_GET = ValueName.Stdlib.operation("List", "get");

    /** Each check is a behavior over one input; {@code wrong} swaps the operation under test for
     *  one that gets it wrong. */
    private static final String PROGRAM = """
            module demo

            data In = { m: Map<String, Int>, k: String, other: String, v: Int,
                        xs: List<Int>, i: Int, wrong: Bool }
            data Out = { holds: Bool }

            behavior insertFilesUnderItsKeyAndLeavesTheRest : (in: In) -> Out
            let insertFilesUnderItsKeyAndLeavesTheRest (in) = {
                let made = if in.wrong
                    then Map.fromList(List.map(kv -> {
                        let (k2, v2) = kv
                        (k2, in.v)
                    }, Map.toList(Map.insert(in.k, in.v, in.m))))
                    else Map.insert(in.k, in.v, in.m)
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
                let listed = if in.wrong
                    then List.map(kv -> {
                        let (k2, v2) = kv
                        (k2, in.v)
                    }, Map.toList(in.m))
                    else Map.toList(in.m)
                Out { holds = Map.fromList(listed) == in.m
                    && List.length(listed) == Map.size(in.m) }
            }

            behavior getAnswersTheValueFiledUnderTheKey : (in: In) -> Out
            let getAnswersTheValueFiledUnderTheKey (in) = {
                let found = if in.wrong then Map.get(in.other, in.m) else Map.get(in.k, in.m)
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
                let found = if in.wrong then List.get(in.i + 1, in.xs) else List.get(in.i, in.xs)
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

    @Test
    void aMapInsertFilesItsValueUnderItsKeyAndLeavesEveryOtherKeyAsItWas() throws Exception {
        runOverTheTable("insertFilesUnderItsKeyAndLeavesTheRest");
    }

    @Test
    void aMapsListHasEachEntryOnceAsItsKeyWithItsValue() throws Exception {
        runOverTheTable("toListPairsEachKeyWithItsValueOnce");
    }

    @Test
    void aMapGetAnswersTheValueFiledUnderItsKey() throws Exception {
        runOverTheTable("getAnswersTheValueFiledUnderTheKey");
    }

    @Test
    void aListGetAnswersTheElementAtItsPlace() throws Exception {
        runOverTheTable("listGetAnswersTheElementAtThePlace");
    }

    /** The behavior {@code name} is true of every input as the library answers it, and false of
     *  some input where the operation it tests is swapped for the wrong one. */
    private static void runOverTheTable(String name) throws Exception {
        WhatTheLibraryComputes.Program program = new WhatTheLibraryComputes.Program("demo",
                PROGRAM);
        List<String> brokenByTheLibrary = new ArrayList<>();
        int caughtOfTheWrongOne = 0;
        for (Map<String, Long> map : maps()) {
            for (String key : List.of("a", "b", "d")) {
                for (long value : List.of(10L, 20L, 30L)) {
                    for (List<Long> list : lists()) {
                        for (long place : List.of(-1L, 0L, 1L, 2L, 5L)) {
                            if (!holds(program, name, map, key, value, list, place, false)) {
                                brokenByTheLibrary.add(name + " " + map + " " + key + " "
                                        + value + " " + list + " " + place);
                            }
                            if (!holds(program, name, map, key, value, list, place, true)) {
                                caughtOfTheWrongOne++;
                            }
                        }
                    }
                }
            }
        }
        assertEquals(List.of(), brokenByTheLibrary, "a kernel answering what the check says");
        assertTrue(caughtOfTheWrongOne > 0,
                "the check is found false of the operation that gets it wrong, or it holds"
                        + " nothing");
    }

    private static boolean holds(WhatTheLibraryComputes.Program program, String name,
                                 Map<String, Long> map, String key, long value, List<Long> list,
                                 long place, boolean wrong) throws Exception {
        Map<String, Object> input = new LinkedHashMap<>();
        input.put("m", map);
        input.put("k", key);
        input.put("other", key.equals("a") ? "b" : "a");
        input.put("v", value);
        input.put("xs", list);
        input.put("i", place);
        input.put("wrong", wrong);
        Map<?, ?> out = (Map<?, ?>) program.answer(name, "In", "Out", input);
        return Boolean.TRUE.equals(out.get("holds"));
    }

    /** Maps over a few keys, each key holding one of two values. */
    private static List<Map<String, Long>> maps() {
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

    private static List<List<Long>> lists() {
        return List.of(List.of(), List.of(7L), List.of(7L, 8L, 9L));
    }

    @Test
    void theTableHoldsMapsThatAreToldApartOnlyByWhichKeyHoldsWhichValue() {
        List<Map<String, Long>> maps = maps();
        assertFalse(maps.get(3).equals(maps.get(4)), "two maps of the same values under other keys");
        assertEquals(maps.get(3).values().stream().sorted().toList(),
                maps.get(4).values().stream().sorted().toList());
    }
}
