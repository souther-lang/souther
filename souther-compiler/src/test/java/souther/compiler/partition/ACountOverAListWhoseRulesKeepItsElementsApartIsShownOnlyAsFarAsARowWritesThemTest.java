package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A list may hold an element over again, and a rule on it may say it does not: no two alike at
 * {@code id}, so two rows of different ids are a list and two of one are none. The count of the
 * elements that meet a statement is then not every value up to how many the list holds, and the
 * number it is held against, {@code k}, is not shown to reach every one of them. A rule that caps
 * how many it holds and says nothing of its elements leaves the count every value up to the cap.
 *
 * <p>The list that is read and those that are not are measured as two models: a model's behaviors
 * share what the measure may spend, so one that spends it on a rule of the elements would leave a
 * count beside it unread for that and not for the rule it is asked about.
 */
class ACountOverAListWhoseRulesKeepItsElementsApartIsShownOnlyAsFarAsARowWritesThemTest {

    private static final String NO_TWO_ALIKE =
            "List.length(List.distinct(List.map(r -> r.id, value))) == List.length(value)";

    /**
     * The behaviors, each by its name, whose {@code k} is not shown to be reached by the count of
     * the rows over five a list holds, where the list is the type a rule of {@code rules} is
     * written on.
     */
    private static Set<String> kNotShown(Map<String, String> rules) {
        StringBuilder source = new StringBuilder("""
                module probe

                data K = Int
                    invariant value >= 0 && value <= 2
                data Row = { id: Int, flag: Bool }
                """);
        rules.forEach((name, rule) -> source.append("""

                data %1$s = List<Row>
                    invariant %2$s
                behavior %1$sCount : (xs: %1$s, k: K) -> Bool
                let %1$sCount (xs, k) = List.length(List.filter(r -> r.id > 5, xs.value)) == k.value
                """.formatted(name, rule)));
        Compilation compilation = Compilation.ofSource(source.toString(), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model under test compiles");
        Map<String, PartitionEvidence> measured =
                compilation.db().ask(new Adequacy.Coverage("probe")).value();
        Set<String> out = new LinkedHashSet<>();
        for (String name : rules.keySet()) {
            PartitionEvidence evidence = measured.get(name + "Count");
            assertNotNull(evidence, name);
            if (evidence.notRead().stream().anyMatch(left -> left.at().equals("k")
                    && left.reason()
                            == UndividedPosition.Reason.RELATION_NOT_SHOWN_TO_REACH_EVERY_VALUE)) {
                out.add(name);
            }
        }
        return out;
    }

    @Test
    void aListCappedAndNothingElseIsShownEveryCountUpToTheCap() {
        assertEquals(Set.of(), kNotShown(Map.of("Capped", "List.length(value) <= 2")));
    }

    @Test
    void aListWhoseElementsARuleKeepsApartIsNotShownEveryCountUpToHowManyItHolds() {
        Map<String, String> rules = new LinkedHashMap<>();
        rules.put("Apart", NO_TWO_ALIKE);
        rules.put("ApartAndCapped", "List.length(value) <= 2 && " + NO_TWO_ALIKE);
        assertEquals(rules.keySet(), kNotShown(rules));
    }
}
