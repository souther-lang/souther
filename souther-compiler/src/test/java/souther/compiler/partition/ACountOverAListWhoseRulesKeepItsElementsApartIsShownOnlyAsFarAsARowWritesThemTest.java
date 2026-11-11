package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A list may hold an element over again, and a rule on it may say it does not: no two alike at
 * {@code id}, so two rows of different ids are a list and two of one are none. The count of the
 * elements that meet a statement is then not every value up to how many the list holds, and the
 * number it is held against is not shown to reach every one of them. A rule that caps how many it
 * holds and says nothing of its elements leaves the count every value up to the cap.
 *
 * <p>The list that is read and those that are not are measured as two models: a model's behaviors
 * share what the measure may spend, so one that spends it on a rule of the elements would leave a
 * count beside it unread for that and not for the rule it is asked about.
 */
class ACountOverAListWhoseRulesKeepItsElementsApartIsShownOnlyAsFarAsARowWritesThemTest {

    private static final String DECLARATIONS = """
            module probe

            data K = Int
                invariant value >= 0 && value <= 2
            data Row = { id: Int, flag: Bool }
            """;

    private static final String NO_TWO_ALIKE =
            "List.length(List.distinct(List.map(r -> r.id, value))) == List.length(value)";

    /** One list type of the model, the number its count is held against, and whether that number
     *  is read. */
    private record Case(String declaration, String against, boolean read) {

        String name() {
            return "L" + Math.abs(declaration.hashCode());
        }
    }

    private static Map<String, Boolean> refused(List<Case> cases) {
        StringBuilder source = new StringBuilder(DECLARATIONS);
        for (Case each : cases) {
            source.append("""

                    data %1$s = List<Row>
                        invariant %2$s
                    behavior %1$s_ : (xs: %1$s, k: K) -> Bool
                    let %1$s_ (xs, k) = List.length(List.filter(r -> r.id > 5, xs.value)) == %3$s
                    """.formatted(each.name(), each.declaration(), each.against()));
        }
        Compilation compilation = Compilation.ofSource(source.toString(), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model under test compiles");
        Map<String, PartitionEvidence> measured =
                compilation.db().ask(new Adequacy.Coverage("probe")).value();
        Map<String, Boolean> out = new LinkedHashMap<>();
        for (Case each : cases) {
            PartitionEvidence evidence = measured.get(each.name() + "_");
            assertNotNull(evidence, each.declaration());
            out.put(each.declaration(), evidence.notRead().stream().anyMatch(left ->
                    left.reason() == UndividedPosition.Reason
                            .RELATION_NOT_SHOWN_TO_REACH_EVERY_VALUE));
        }
        return out;
    }

    @Test
    void aListCappedAndNothingElseIsShownEveryCountUpToTheCap() {
        Case capped = new Case("List.length(value) <= 2", "k.value", true);
        assertEquals(Map.of(capped.declaration(), false), refused(List.of(capped)));
    }

    @Test
    void aListWhoseElementsARuleKeepsApartIsNotShownEveryCountUpToHowManyItHolds() {
        Case apart = new Case(NO_TWO_ALIKE, "k.value", false);
        Case apartAndCapped = new Case("List.length(value) <= 2 && " + NO_TWO_ALIKE, "k.value",
                false);
        assertEquals(Map.of(apart.declaration(), true, apartAndCapped.declaration(), true),
                refused(List.of(apart, apartAndCapped)));
    }
}
