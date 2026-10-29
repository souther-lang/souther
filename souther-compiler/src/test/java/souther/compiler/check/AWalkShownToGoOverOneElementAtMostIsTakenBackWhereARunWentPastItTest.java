package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.coverage.Numberings;
import souther.compiler.coverage.SiteNumbering;
import souther.compiler.coverage.WalkProbe;

import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A walk shown to go over one element at most is no longer shown so where a run took a second
 * element of its list: a proof a run went against closes nothing, as it does for an arm.
 */
class AWalkShownToGoOverOneElementAtMostIsTakenBackWhereARunWentPastItTest {

    private static final SiteNumbering NUMBERING =
            Numberings.of(Numberings.Family.WALK, Numberings.Family.WALK);

    private static final WalkProbe HERE = NUMBERING.walk(0);
    private static final WalkProbe THERE = NUMBERING.walk(1);

    private static PathReachability.Answers shownAtBoth() {
        Optional<souther.compiler.coverage.NumberingIdentity> numbering =
                Optional.of(HERE.numbering());
        return new PathReachability.Answers(numbering, Map.of(),
                new PathReachability.Arrivals(numbering, Map.of(), Map.of(), Map.of(),
                        Set.of(HERE, THERE)));
    }

    @Test
    void aWalkNoRunWentPastIsStillShown() {
        assertEquals(Set.of(HERE, THERE), shownAtBoth().asRunWith(Set.of(), Set.of(), Set.of())
                .answers().arrivals().walksHeldToOneAtMost());
    }

    @Test
    void aWalkARunTookASecondElementOfIsNoLongerShown() {
        assertEquals(Set.of(THERE), shownAtBoth().asRunWith(Set.of(), Set.of(), Set.of(HERE))
                .answers().arrivals().walksHeldToOneAtMost());
    }
}
