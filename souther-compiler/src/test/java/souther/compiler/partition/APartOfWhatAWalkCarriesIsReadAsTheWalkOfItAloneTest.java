package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A part of what a walk carries — a field of a record or a component of a tuple — whose step reads
 * nothing else carried is read as the same walk carrying that part alone: a rule over how many it
 * holds or what it adds up to comes to what the rule over the walk of it alone comes to. A part
 * whose step reads another part is no walk of its own, and its rule is not read as one.
 *
 * <p>The walk of the part alone is the oracle. Each model below is judged beside the one carrying
 * the part alone, and what each leaves unread has to be the same, place for place and word for
 * word.
 */
class APartOfWhatAWalkCarriesIsReadAsTheWalkOfItAloneTest {

    private static final String DECLARATIONS = """
            module probe

            data Item = { code: String, price: Int }
            data Prices = { known: Map<String, Int> }
            data Two = { xs: List<String>, ys: List<String> }
            data Sums = { s: Int, c: Int }
            data Inner = { ys: List<String> }
            data Outer = { inner: Inner, n: Int }
            """;

    /** A rule over what the walk comes to, beside a rule the run gets to past the walk. */
    private static final String JUDGED = """

            behavior %1$s : (items: List<Item>, prices: Prices) -> Bool
            let %1$s (items, prices) = {
                %2$s
                    && List.all(i -> Map.containsKey(i.code, prices.known), items)
            }
            """;

    private static final String LIST_ALONE =
            "List.length(List.fold((acc, i) -> acc ++ [i.code], [], items)) >= 0";

    private static final String SUM_ALONE = "List.fold((acc, i) -> acc + i.price, 0, items) >= 0";

    /** What each of {@code judged} leaves unread, by the behavior's name. */
    private static Map<String, List<String>> unread(Map<String, String> judged) {
        StringBuilder source = new StringBuilder(DECLARATIONS);
        judged.forEach((name, rule) -> source.append(JUDGED.formatted(name, rule)));
        Compilation compilation = Compilation.ofSource(source.toString(), "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        Map<String, PartitionEvidence> evidence =
                compilation.db().ask(new Adequacy.Coverage("probe")).value();
        // A body that does not type is no body read, and leaves nothing unread.
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the models under test compile");
        Map<String, List<String>> out = new LinkedHashMap<>();
        judged.keySet().forEach(name -> out.put(name, evidence.get(name).notRead().stream()
                .map(each -> each.at() + "=" + each.reason()).toList()));
        return out;
    }

    /** A tuple pattern taking the part apart, a branch answering what was carried, and a part
     *  of a part, each as the walk of the part alone. */
    @Test
    void aPartWhoseStepReadsNothingElseCarriedIsTheWalkOfItAlone() {
        Map<String, String> judged = new LinkedHashMap<>();
        judged.put("listAlone", LIST_ALONE);
        judged.put("sumAlone", SUM_ALONE);
        judged.put("chosenAlone", "List.fold((acc, i) -> "
                + "if i.price > 0 then acc + 1 else acc, 0, items) >= 0");
        judged.put("listInATuple", "List.length({\n"
                + "        let (_, ys) = List.fold((acc, i) -> {\n"
                + "            let (xs, ys) = acc\n"
                + "            (xs, ys ++ [i.code])\n"
                + "        }, ([], []), items)\n"
                + "        ys\n"
                + "    }) >= 0");
        judged.put("listInARecord", "List.length(List.fold((acc, i) -> "
                + "Two { xs = acc.xs, ys = acc.ys ++ [i.code] }, Two { xs = [], ys = [] },"
                + " items).ys) >= 0");
        judged.put("sumInATuple", "{\n"
                + "        let (s, _) = List.fold((acc, i) -> {\n"
                + "            let (s, c) = acc\n"
                + "            (s + i.price, c)\n"
                + "        }, (0, 0), items)\n"
                + "        s\n"
                + "    } >= 0");
        judged.put("sumInARecord", "List.fold((acc, i) -> "
                + "Sums { s = acc.s + i.price, c = acc.c }, Sums { s = 0, c = 0 }, items).s >= 0");
        judged.put("chosenInATuple", "{\n"
                + "        let (s, _) = List.fold((acc, i) -> {\n"
                + "            let (s, c) = acc\n"
                + "            if i.price > 0 then (s + 1, c) else acc\n"
                + "        }, (0, 0), items)\n"
                + "        s\n"
                + "    } >= 0");
        judged.put("matchedAlone", "List.fold((acc, i) -> {\n"
                + "            match Map.get(i.code, prices.known) with\n"
                + "            | Some p -> acc + 1\n"
                + "            | None -> acc\n"
                + "        }, 0, items) >= 0");
        judged.put("matchedInATuple", "{\n"
                + "        let (s, _) = List.fold((acc, i) -> {\n"
                + "            let (s, c) = acc\n"
                + "            match Map.get(i.code, prices.known) with\n"
                + "            | Some p -> (s + 1, c)\n"
                + "            | None -> acc\n"
                + "        }, (0, 0), items)\n"
                + "        s\n"
                + "    } >= 0");
        judged.put("listInAPartOfARecord", "List.length(List.fold((acc, i) -> "
                + "Outer { inner = Inner { ys = acc.inner.ys ++ [i.code] }, n = acc.n },"
                + " Outer { inner = Inner { ys = [] }, n = 0 }, items).inner.ys) >= 0");
        Map<String, List<String>> unread = unread(judged);

        for (String part : List.of("listInATuple", "listInARecord", "listInAPartOfARecord")) {
            assertEquals(unread.get("listAlone"), unread.get(part), part);
        }
        for (String part : List.of("sumInATuple", "sumInARecord")) {
            assertEquals(unread.get("sumAlone"), unread.get(part), part);
        }
        assertEquals(unread.get("chosenAlone"), unread.get("chosenInATuple"));
        assertEquals(unread.get("matchedAlone"), unread.get("matchedInATuple"));
    }

    /** A part whose step reads another part carried, or the part taken being another than the
     *  one the step builds from what was carried, is no walk of its own. */
    @Test
    void aPartWhoseStepReadsAnotherPartIsNotReadAsAWalk() {
        Map<String, String> judged = new LinkedHashMap<>();
        judged.put("listAlone", LIST_ALONE);
        judged.put("growsByTheOther", "List.length({\n"
                + "        let (_, ys) = List.fold((acc, i) -> {\n"
                + "            let (xs, ys) = acc\n"
                + "            (xs ++ [i.code], ys ++ xs)\n"
                + "        }, ([\"\"], [\"\"]), items)\n"
                + "        ys\n"
                + "    }) >= 0");
        judged.put("swapped", "List.length({\n"
                + "        let (xs, _) = List.fold((acc, i) -> {\n"
                + "            let (xs, ys) = acc\n"
                + "            (ys, xs ++ [i.code])\n"
                + "        }, ([\"\"], [\"\"]), items)\n"
                + "        xs\n"
                + "    }) >= 0");
        Map<String, List<String>> unread = unread(judged);

        for (String part : List.of("growsByTheOther", "swapped")) {
            assertTrue(unread.get(part).stream().anyMatch(each ->
                            each.endsWith("=" + UndividedPosition.Reason.RULE_MEASURED_ON_ITS_RUNS)),
                    part + " " + unread.get(part));
        }
    }
}
