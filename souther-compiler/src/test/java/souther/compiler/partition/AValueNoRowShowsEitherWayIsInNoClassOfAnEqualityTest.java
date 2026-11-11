package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.numeric.Count;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What an equality beside a total tells of a number is read off the classes the partition draws,
 * and a value neither shown to be one the equality holds at nor shown to be none is in no class.
 *
 * <p>One element of {@code 0..10} doubled comes to the evens up to twenty, and several elements
 * come to any even number from nought. So twenty-four is a total the rows do not show and nothing
 * rules out: a class that held it as one the equality never holds at would be a claim about a
 * value a program can reach.
 */
class AValueNoRowShowsEitherWayIsInNoClassOfAnEqualityTest {

    private static final String SOURCE = """
            module probe
            data Item = { v: Int }
                invariant low = v >= 0
                invariant high = v <= 10
            behavior check : (items: List<Item>, cap: Int) -> Bool
            let check (items, cap) = List.sum(List.map(i -> i.v * 2, items)) == cap
            """;

    /** The classes the model's body divides {@code cap} into, which is what a reader is handed. */
    private static List<PartitionClass> classesOfCap() {
        Compilation compilation = Compilation.ofSource(SOURCE, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Partitions.Partitioning partitioning = compilation.db()
                .ask(new Adequacy.Divided(compilation.modules().get(0), "check")).value();
        assertNotNull(partitioning, "the body divides a position");
        List<PartitionClass> classes = partitioning.axes().stream()
                .filter(axis -> axis.path().toString().equals("cap"))
                .flatMap(axis -> axis.classes().stream()).toList();
        assertFalse(classes.isEmpty(), "the equality divides cap: " + partitioning.axes());
        return classes;
    }

    private static boolean holds(PartitionClass each, long number) {
        return each.recognises().numbers().holds(Count.of(number), Carrier.WHOLE);
    }

    @Test
    void theClassesAreTheNumbersShownAndTheNumbersShownNever() {
        List<PartitionClass> classes = classesOfCap();
        assertEquals(2, classes.size(), classes.toString());
        PartitionClass canBe = classes.stream().filter(each -> each.label().contains("can be"))
                .findFirst().orElseThrow();
        PartitionClass never = classes.stream().filter(each -> each.label().contains("never"))
                .findFirst().orElseThrow();
        for (long even : new long[] {0, 2, 10, 20}) {
            assertTrue(holds(canBe, even), "an even number one element reaches: " + even);
            assertFalse(holds(never, even), "is no number the equality never holds at: " + even);
        }
        for (long odd : new long[] {-3, -1, 1, 3, 21}) {
            assertTrue(holds(never, odd), "an odd number no total is: " + odd);
            assertFalse(holds(canBe, odd), "is no number the equality can hold at: " + odd);
        }
    }

    /** A total of several elements is twenty-four, which no row shows: it is in neither class. */
    @Test
    void anEvenNumberOnlySeveralElementsReachIsInNeitherClass() {
        for (PartitionClass each : classesOfCap()) {
            assertFalse(holds(each, 24), each.label() + " holds 24, which no row shows either way");
            assertFalse(holds(each, 22), each.label() + " holds 22, which no row shows either way");
        }
    }
}
