package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.coverage.NumberingIdentity;
import souther.compiler.coverage.Numberings;
import souther.compiler.coverage.ReachEvidence;
import souther.compiler.coverage.SiteNumbering;
import souther.compiler.coverage.WalkProbe;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.WrittenOwner;

import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A walk shown to go over one element at most is no longer shown so where a run took a second
 * element of its list, and the proof the run went against is written down as one: a proof a run
 * went against closes nothing and is not lost, as it is for an arm.
 */
class AWalkShownToGoOverOneElementAtMostIsTakenBackWhereARunWentPastItTest {

    private static final SiteNumbering NUMBERING =
            Numberings.of(Numberings.Family.WALK, Numberings.Family.WALK);

    private static final WalkProbe HERE = NUMBERING.walk(0);
    private static final WalkProbe THERE = NUMBERING.walk(1);

    private static final SourceConstructOrigin FOLD = SourceConstructOrigin.written(
            new WrittenOwner.Body("fixture", "sum"), 0, SourceConstruct.CALL);
    private static final SourceConstructOrigin ANOTHER_FOLD = SourceConstructOrigin.written(
            new WrittenOwner.Body("fixture", "total"), 1, SourceConstruct.CALL);

    private static PathReachability.Answers shownAtBoth() {
        Optional<NumberingIdentity> numbering = Optional.of(HERE.numbering());
        return new PathReachability.Answers(numbering, Map.of(),
                new PathReachability.Arrivals(numbering, Map.of(), Map.of(), Map.of(),
                        Map.of(HERE, FOLD, THERE, ANOTHER_FOLD)));
    }

    @Test
    void aWalkNoRunWentPastIsStillShownAndNothingIsContradicted() {
        PathReachability.Answers.AsRun ran =
                shownAtBoth().asRunWith(ReachEvidence.NONE);

        assertEquals(Set.of(HERE, THERE), ran.answers().arrivals().walksHeldToOneAtMost().keySet());
        assertEquals(PathReachability.Answers.Contradictions.NONE, ran.contradicted());
    }

    @Test
    void aWalkARunTookASecondElementOfIsNoLongerShownAndIsContradicted() {
        PathReachability.Answers.AsRun ran =
                shownAtBoth().asRunWith(
                        ReachEvidence.of(Set.of(), Set.of(), Set.of(HERE)));

        assertEquals(Set.of(THERE), ran.answers().arrivals().walksHeldToOneAtMost().keySet());
        assertEquals(Set.of(FOLD), ran.contradicted().walks());
        assertEquals(true, ran.contradicted().reachIsEmpty(),
                "a proof about a list is no proof of where anything arrives");
    }

    /** A run past a walk nothing was shown of goes against nothing. */
    @Test
    void aWalkNothingWasShownOfIsNeverContradicted() {
        Optional<NumberingIdentity> numbering = Optional.of(HERE.numbering());
        PathReachability.Answers shownAtNone = new PathReachability.Answers(numbering, Map.of(),
                new PathReachability.Arrivals(numbering, Map.of(), Map.of(), Map.of(), Map.of()));

        assertEquals(PathReachability.Answers.Contradictions.NONE,
                shownAtNone.asRunWith(
                        ReachEvidence.of(Set.of(), Set.of(), Set.of(HERE, THERE))).contradicted());
    }
}
