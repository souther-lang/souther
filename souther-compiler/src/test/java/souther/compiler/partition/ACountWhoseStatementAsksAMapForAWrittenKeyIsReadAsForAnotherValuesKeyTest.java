package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

import souther.compiler.ACompiledModel;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A count of the elements whose map holds a key is read the same whether the key is the element's
 * own field, an input, or written in the statement. A key written stands at no position of the
 * row, so what the map is asked is that it hold the value, or not hold it — two classes of the
 * map's place, as a key the element names is — and the count is held against a number that reaches
 * every value from none up to how many elements there are.
 *
 * <p>Where the map is not the element's but one beside the lines, every element asks it the same
 * thing, so the count is none or all of them and no number between. That is a count a number
 * between is not shown to reach, whatever the key is written as.
 */
class ACountWhoseStatementAsksAMapForAWrittenKeyIsReadAsForAnotherValuesKeyTest {

    private static final String DECLARATIONS = """
            module probe

            data Code = String

            data Line = { code: String, rates: Map<String, Int>, tags: List<String>,
                          nums: Set<Int>, amts: List<Decimal>, flags: List<Bool>,
                          coded: Map<Code, Int>, cc: Code }

            let usd = "USD"
            let usdCode = Code("USD")
            """;

    private static final String BEHAVIOR = """

            behavior %1$s : (lines: List<Line>, rates: Map<String, Int>, k: Int,
                             key: String) -> Bool
            let %1$s (lines, rates, k, key) = %2$s
            """;

    /** A count, whether the number it is held against is shown to reach every value. */
    private record Case(String body, boolean reaches) {}

    private static final List<Case> CASES = List.of(
            // The key is another value of the row.
            new Case("List.length(List.filter(l -> Map.containsKey(l.code, l.rates), lines))"
                    + " == k", true),
            new Case("List.length(List.filter(l -> Map.containsKey(key, l.rates), lines))"
                    + " == k", true),
            // The key is written.
            new Case("List.length(List.filter(l -> Map.containsKey(\"USD\", l.rates), lines))"
                    + " == k", true),
            // More values written than the search tries subsets of: the ones a statement is
            // likeliest to need are those at the ends, all of them and all but one.
            new Case("List.length(List.filter(l -> " + allOf(9) + ", lines)) == k", true),
            new Case("List.length(List.filter(l -> Bool.not(" + allOf(9) + "), lines)) == k",
                    true),
            // So many that the subsets of them are more than could be walked one by one.
            new Case("List.length(List.filter(l -> " + allOf(40) + ", lines)) == k", true),
            // A value written under a name is the value it is.
            new Case("List.length(List.filter(l -> Map.containsKey(usd, l.rates), lines)) == k",
                    true),
            // A map keyed by a newtype, the key another value of the row or a newtype's
            // constructor written in the statement or under a name.
            new Case("List.length(List.filter(l -> Map.containsKey(l.cc, l.coded), lines))"
                    + " == k", true),
            new Case("List.length(List.filter(l -> Map.containsKey(Code(\"USD\"), l.coded),"
                    + " lines)) == k", true),
            new Case("List.length(List.filter(l -> Map.containsKey(usdCode, l.coded), lines))"
                    + " == k", true),
            // A key made of a value of the row is worked out of it and is no value written.
            new Case("List.length(List.filter(l -> Map.containsKey(Code(l.code), l.coded),"
                    + " lines)) == k", false),
            // The same of the elements a list or a set holds, of any kind of value written.
            new Case("List.length(List.filter(l -> List.contains(\"K\", l.tags), lines)) == k",
                    true),
            new Case("List.length(List.filter(l -> Set.contains(7, l.nums), lines)) == k", true),
            new Case("List.length(List.filter(l -> List.contains(1.5m, l.amts), lines)) == k",
                    true),
            new Case("List.length(List.filter(l -> List.contains(true, l.flags), lines)) == k",
                    true),
            // Several values written at one container: the elements holding all of them, some of
            // them, and none are each a class of the container.
            new Case("List.length(List.filter(l -> Map.containsKey(\"USD\", l.rates)"
                    + " && Map.containsKey(\"EUR\", l.rates), lines)) == k", true),
            new Case("List.length(List.filter(l -> Map.containsKey(\"USD\", l.rates)"
                    + " && Bool.not(Map.containsKey(\"EUR\", l.rates)), lines)) == k", true),
            new Case("List.length(List.filter(l -> List.contains(\"K\", l.tags)"
                    + " && List.contains(\"L\", l.tags), lines)) == k", true),
            new Case("List.length(List.filter(l -> Set.contains(7, l.nums)"
                    + " || Set.contains(8, l.nums), lines)) == k", true),
            // The same collection asked to hold a value and to hold so many: the one value is
            // among the three.
            new Case("List.length(List.filter(l -> List.length(l.tags) == 3"
                    + " && List.contains(\"USD\", l.tags), lines)) == k", true),
            new Case("List.length(List.filter(l -> Set.size(l.nums) == 2"
                    + " && Set.contains(7, l.nums), lines)) == k", true),
            // A map that must not hold the key is the other class of the same place.
            new Case("List.length(List.filter(l -> Bool.not(Map.containsKey(\"USD\", l.rates)),"
                    + " lines)) == k", true),
            // A statement no element meets is a count no row holds at anything but none.
            new Case("List.length(List.filter(l -> Map.containsKey(\"USD\", l.rates)"
                    + " && Bool.not(Map.containsKey(\"USD\", l.rates)), lines)) == k", false),
            // One map beside the lines is asked the same by every element.
            new Case("List.length(List.filter(l -> Map.containsKey(\"USD\", rates), lines))"
                    + " == k", false),
            new Case("List.length(List.filter(l -> Map.containsKey(key, rates), lines))"
                    + " == k", false));

    /** A map holding every one of {@code many} keys written. */
    private static String allOf(int many) {
        return java.util.stream.IntStream.rangeClosed(1, many)
                .mapToObj(each -> "Map.containsKey(\"K" + each + "\", l.rates)")
                .collect(java.util.stream.Collectors.joining(" && "));
    }

    private static Map<String, PartitionEvidence> measured() {
        StringBuilder source = new StringBuilder(DECLARATIONS);
        int at = 0;
        for (Case each : CASES) {
            source.append(BEHAVIOR.formatted("case" + at++, each.body()));
        }
        Compilation compilation = Compilation.ofSource(source.toString(), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        return compilation.db().ask(new Adequacy.Coverage("probe")).value();
    }

    /** The time is bounded in the statements a model writes, whatever number of values it names:
     *  the subsets of them are made and not walked to. */
    @Test
    @Timeout(value = 60, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    void aCountIsHeldAgainstANumberThatReachesEveryValueWhereARowShowsEveryCount() {
        Map<String, PartitionEvidence> measured = measured();
        Map<String, Boolean> shown = new LinkedHashMap<>();
        int at = 0;
        for (Case each : CASES) {
            PartitionEvidence evidence = measured.get("case" + at++);
            assertNotNull(evidence, each.body());            shown.put(each.body(), evidence.notRead().stream().noneMatch(left ->
                    left.at().equals("k")));
        }
        Map<String, Boolean> expected = new LinkedHashMap<>();
        CASES.forEach(each -> expected.put(each.body(), each.reaches()));
        Map<String, Boolean> differing = new LinkedHashMap<>(shown);
        differing.entrySet().removeIf(each -> each.getValue().equals(expected.get(each.getKey())));
        assertEquals(Map.of(), differing, "the cases shown otherwise than expected, as shown");
    }
}
