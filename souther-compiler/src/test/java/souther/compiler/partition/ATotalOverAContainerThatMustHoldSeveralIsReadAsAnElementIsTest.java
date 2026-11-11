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
 * A total over the elements of a container takes every value one element is shown to take where
 * the container may hold one element, since the total is then that element. Where the rules ask
 * it for two or more, the rest are at nought, which the total adds nothing for: the total is the
 * one element's value again, so long as nought is a value an element takes and the container may
 * hold a value more than once.
 *
 * <p>The controls keep the numbers small, so that the run the total is shown to take is the whole
 * of what {@code cap} is asked to be reached at: a run shown past what the rows make is then a
 * number {@code cap} is read reached at that no row holds. Held apart, the rest are not at
 * nought and the least total is one, and with no nought among the elements it is two.
 */
class ATotalOverAContainerThatMustHoldSeveralIsReadAsAnElementIsTest {

    private static final String DECLARATIONS = """
            module probe

            data Cap = Int
                invariant value >= 0 && value <= 3
            data Small = Int
                invariant value >= 0 && value <= 3
            data Positive = Int
                invariant value >= 1 && value <= 3

            data Two = List<Int>
                invariant List.length(value) >= 2
            data Three = List<Int>
                invariant List.length(value) >= 3
            data TwoSmall = List<Small>
                invariant List.length(value) >= 2
            data ApartSmall = List<Small>
                invariant List.length(value) >= 2 && Set.size(Set.fromList(value)) == List.length(value)
            data PositiveSmall = List<Positive>
                invariant List.length(value) >= 2
            """;

    private static final String BEHAVIOR = """

            behavior %1$s : (xs: %2$s, cap: %4$s) -> Bool
            let %1$s (xs, cap) = %3$s
            """;

    /** A container, how a total over it is held against {@code cap} and the type of {@code cap},
     *  and whether {@code cap} is read. */
    private record Case(String type, String statement, String cap, boolean read) {}

    private static final Map<String, Case> CASES = cases();

    private static Map<String, Case> cases() {
        Map<String, Case> out = new LinkedHashMap<>();
        out.put("aPlainList", new Case("List<Int>", "List.sum(xs) <= cap", "Int", true));
        out.put("twoOrMore", new Case("Two", "List.sum(xs.value) <= cap", "Int", true));
        out.put("threeOrMore", new Case("Three", "List.sum(xs.value) <= cap", "Int", true));
        out.put("twoOrMoreSmall", new Case("TwoSmall",
                "List.sum(List.map(x -> x.value, xs.value)) >= cap.value", "Cap", true));
        // Held apart the least total is one, and no total of nought is a total.
        out.put("heldApart", new Case("ApartSmall",
                "List.sum(List.map(x -> x.value, xs.value)) >= cap.value", "Cap", false));
        // With no nought among the elements the least total is two.
        out.put("noNoughtAmongTheElements", new Case("PositiveSmall",
                "List.sum(List.map(x -> x.value, xs.value)) >= cap.value", "Cap", false));
        return out;
    }

    private static final Map<String, PartitionEvidence> MEASURED = measured();

    private static Map<String, PartitionEvidence> measured() {
        StringBuilder source = new StringBuilder(DECLARATIONS);
        CASES.forEach((name, each) -> source.append(
                BEHAVIOR.formatted(name, each.type(), each.statement(), each.cap())));
        Compilation compilation = Compilation.ofSource(source.toString(), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model under test compiles");
        Map<String, PartitionEvidence> out =
                compilation.db().ask(new Adequacy.Coverage("probe")).value();
        assertNotNull(out, "the model under test compiles");
        return out;
    }

    @Test
    void aTotalIsAnElementsValueAgainWhereTheOthersAreAtNoughtAndNoneIsHeldApart() {
        Map<String, Boolean> refused = new LinkedHashMap<>();
        CASES.forEach((name, each) -> {
            PartitionEvidence evidence = MEASURED.get(name);
            assertNotNull(evidence, name);
            refused.put(name, evidence.notRead().stream().anyMatch(left ->
                    left.at().startsWith("cap")
                            && left.reason() == UndividedPosition.Reason
                                    .RELATION_NOT_SHOWN_TO_REACH_EVERY_VALUE));
        });
        Map<String, Boolean> expected = new LinkedHashMap<>();
        CASES.forEach((name, each) -> expected.put(name, !each.read()));
        assertEquals(expected, refused);
    }
}
