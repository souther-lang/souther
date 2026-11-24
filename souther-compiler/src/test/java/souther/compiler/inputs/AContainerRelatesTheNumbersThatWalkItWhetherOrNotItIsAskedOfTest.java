package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two things are said of a container and they are two: it relates the numbers that walk it, and
 * it is asked of each way only where nothing settles how it holds. A container settled by what the
 * question stands under is no case to look at and is still a reason two numbers are one question:
 * what a total comes to as the totals of its places is put on when a number is asked of, and
 * relates numbers of one container whatever the rules say.
 */
class AContainerRelatesTheNumbersThatWalkItWhetherOrNotItIsAskedOfTest {

    private static final TermPath K = TermPath.of("b").then("xs");
    private static final TermPath OTHER = TermPath.of("b").then("ys");

    @Test
    void numbersOfDifferentPartsWalkingASettledContainerAreOneGroupAndItIsNotAskedOf() {
        ContainerGroups groups = new ContainerGroups();
        groups.say("total", 0, K, true, true);
        groups.say("first", 1, K, true, true);
        groups.say("second", 2, K, true, true);

        assertEquals(groups.keyOf("total"), groups.keyOf("first"));
        assertEquals(groups.keyOf("total"), groups.keyOf("second"));
        assertEquals(List.of(), groups.groups(), "a settled container is no case to look at");
        assertEquals(List.of(), groups.containersOf(groups.keyOf("total")));
    }

    @Test
    void theSameNumbersWalkingAnOpenContainerAreOneGroupAndItIsAskedOf() {
        ContainerGroups groups = new ContainerGroups();
        groups.say("total", 0, K, false, true);
        groups.say("first", 1, K, false, true);

        assertEquals(groups.keyOf("total"), groups.keyOf("first"));
        assertEquals(List.of(new ContainerGroups.Group(List.of(K), true)), groups.groups());
        assertEquals(List.of(K), groups.containersOf(groups.keyOf("total")));
    }

    @Test
    void numbersOfOnePartWalkingDifferentContainersAreOneGroupAskedOfBoth() {
        ContainerGroups groups = new ContainerGroups();
        groups.say("a", 7, K, false, true);
        groups.say("b", 7, OTHER, false, true);

        assertEquals(groups.keyOf("a"), groups.keyOf("b"));
        assertEquals(List.of(new ContainerGroups.Group(List.of(K, OTHER), true)), groups.groups());
    }

    @Test
    void numbersOfDifferentPartsWalkingDifferentContainersAreGroupsOfTheirOwn() {
        ContainerGroups groups = new ContainerGroups();
        groups.say("a", 1, K, false, true);
        groups.say("b", 2, OTHER, false, false);

        assertNotEquals(groups.keyOf("a"), groups.keyOf("b"));
        assertEquals(List.of(new ContainerGroups.Group(List.of(K), true),
                new ContainerGroups.Group(List.of(OTHER), false)), groups.groups());
    }

    @Test
    void aNumberNoPartWeighsIsAGroupOfItsOwnAndWalksNoContainer() {
        ContainerGroups groups = new ContainerGroups();
        groups.say("loose", null, null, false, true);

        assertEquals("loose", groups.keyOf("loose"));
        assertTrue(groups.groups().isEmpty());
    }
}
