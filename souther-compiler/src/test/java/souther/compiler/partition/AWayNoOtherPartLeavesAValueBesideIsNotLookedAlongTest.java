package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.partition.WaysThatLeaveAValueBesideTheRest.Beside;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Predicate;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * No row holds the parts of a way together where some part has no way of holding it that another
 * part's ways leave a value beside, and only where every way the part had was looked at. A part
 * short of ways because a figure left them out says the figure and proves nothing.
 *
 * <p>The ways are told apart by the position they are of, and what two of them leave together is
 * said by the pairs the test names as leaving none.
 */
class AWayNoOtherPartLeavesAValueBesideIsNotLookedAlongTest {

    private static final HeldOutcome A = HeldOutcomeFixtures.aWayAt("a");
    private static final HeldOutcome B = HeldOutcomeFixtures.aWayAt("b");
    private static final HeldOutcome C = HeldOutcomeFixtures.aWayAt("c");
    private static final HeldOutcome D = HeldOutcomeFixtures.aWayAt("d");

    private static final Set<CompositionBudget> A_FIGURE =
            Set.of(CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT);

    /** Everything leaves a value but the pairs named, which are pairs of ways and not of parts. */
    private static Predicate<List<HeldOutcome>> leavingNoneOf(List<Set<HeldOutcome>> pairs) {
        return held -> !(held.size() == 2 && pairs.contains(new HashSet<>(held)));
    }

    @Test
    void aPartEveryWayOfWhichAnotherPartLeavesNoValueBesideSaysNoRowHoldsThem() {
        Beside came = WaysThatLeaveAValueBesideTheRest.of(List.of(List.of(A), List.of(B, C)),
                Set.of(), leavingNoneOf(List.of(Set.of(A, B), Set.of(A, C))));

        assertEquals(new Beside.NoneHolds(), came);
    }

    /** A way is kept where some way of each other part leaves a value beside it. */
    @Test
    void aWayStaysWhereAnyWayOfEachOtherPartLeavesAValueBesideIt() {
        Beside came = WaysThatLeaveAValueBesideTheRest.of(List.of(List.of(A, D), List.of(B)),
                Set.of(), leavingNoneOf(List.of(Set.of(A, B))));

        assertEquals(new Beside.Remaining(List.of(List.of(D), List.of(B))), came);
    }

    /** Parts each leave a value beside every other, and the three together leave none: that is
     *  not asked here, and so is not said. */
    @Test
    void partsThatLeaveAValueTwoAtATimeAreNotSaidToLeaveNone() {
        List<List<HeldOutcome>> parts = List.of(List.of(A), List.of(B), List.of(C));
        List<Integer> asked = new ArrayList<>();
        Predicate<List<HeldOutcome>> leaves = held -> {
            asked.add(held.size());
            return true;
        };

        assertEquals(new Beside.Remaining(parts),
                WaysThatLeaveAValueBesideTheRest.of(parts, Set.of(), leaves));
        assertTrue(asked.stream().allMatch(size -> size <= 2), () -> "only ones and pairs: " + asked);
    }

    /** Where a figure left ways out, a part with none left is the figure and not a proof. */
    @Test
    void aPartWithNoneLeftWhereAFigureLeftWaysOutIsTheFigureAndNoProof() {
        Beside came = WaysThatLeaveAValueBesideTheRest.of(List.of(List.of(A), List.of(B)),
                A_FIGURE, leavingNoneOf(List.of(Set.of(A, B))));

        assertEquals(new Beside.NotEveryWayWasLookedAt(A_FIGURE), came);
    }

    /** Two parts are two parts whichever list they are given as. */
    @Test
    void twoPartsGivenAsOneListAreTwoParts() {
        List<HeldOutcome> one = List.of(A);

        Beside came = WaysThatLeaveAValueBesideTheRest.of(List.of(one, one), Set.of(),
                leavingNoneOf(List.of(Set.of(A))));

        assertEquals(new Beside.NoneHolds(), came);
    }

    /** A decision nothing can state a demand for is left out, and what is left proves it. */
    @Test
    void aDecisionWithNoDemandReadDoesNotKeepTheOthersFromProvingNoRowHoldsThem() {
        List<HeldOutcome.Bringing> readable = ReadableDemands.of(List.of(
                new HeldOutcome.Bringing.Found(List.of(A), Set.of()),
                new HeldOutcome.Bringing.NothingFound(),
                new HeldOutcome.Bringing.Found(List.of(B), Set.of()))).readable();
        List<List<HeldOutcome>> parts = readable.stream()
                .map(each -> ((HeldOutcome.Bringing.Found) each).ways()).toList();

        assertEquals(new Beside.NoneHolds(), WaysThatLeaveAValueBesideTheRest.of(parts, Set.of(),
                leavingNoneOf(List.of(Set.of(A, B)))));
    }
}
