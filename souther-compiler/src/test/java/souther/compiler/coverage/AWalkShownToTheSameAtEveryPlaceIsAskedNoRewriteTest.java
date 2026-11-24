package souther.compiler.coverage;

import org.junit.jupiter.api.Test;

import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.WrittenOwner;

import java.util.Optional;
import java.util.Set;
import java.util.TreeMap;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A walk is asked no rewrite where what holds on the way shows it the walk under either spelling at
 * every place it is entered, and is asked as before where any place shows nothing.
 *
 * <p>Asked of the rewrites themselves, which is where the measure of the rows written and the
 * choosing of a row to offer both ask it: one answer to which rewrites a walk owes, and no reader
 * holding a proof the other does not.
 */
class AWalkShownToTheSameAtEveryPlaceIsAskedNoRewriteTest {

    private static final SourceConstructOrigin FOLD = SourceConstructOrigin.written(
            new WrittenOwner.Body("fixture", "sum"), 0, SourceConstruct.CALL);

    private static final SiteNumbering NUMBERING =
            Numberings.of(Numberings.Family.WALK, Numberings.Family.WALK);

    private static final WalkProbe HERE = NUMBERING.walk(0);
    private static final WalkProbe THERE = NUMBERING.walk(1);

    /** One fold, written once, entered at two places. */
    private static WalkRewrites foldEnteredTwice() {
        TreeMap<Integer, WalkRewrites.AtWalk> bySite = new TreeMap<>();
        bySite.put(0, new WalkRewrites.AtWalk(FOLD, HERE, Set.of(), false, Optional.empty()));
        bySite.put(1, new WalkRewrites.AtWalk(FOLD, THERE, Set.of(), false, Optional.empty()));
        return new WalkRewrites(bySite);
    }

    private static int asked(WalkRewrites rewrites) {
        return rewrites.askedOf(FOLD, WalkedNoFurther.NOTHING).size();
    }

    @Test
    void aWalkNothingIsShownOfIsAskedBothRewrites() {
        assertEquals(2, asked(foldEnteredTwice()));
        assertEquals(2, asked(foldEnteredTwice().provingTheSameAt(Set.of())));
    }

    @Test
    void aWalkShownAtEveryPlaceItIsEnteredIsAskedNeither() {
        assertEquals(0, asked(foldEnteredTwice().provingTheSameAt(Set.of(HERE, THERE))));
    }

    @Test
    void aWalkShownAtOnePlaceOnlyIsAskedBothRewritesStill() {
        assertEquals(2, asked(foldEnteredTwice().provingTheSameAt(Set.of(HERE))));
        assertEquals(2, asked(foldEnteredTwice().provingTheSameAt(Set.of(THERE))));
    }

    /** What the proof is applied to is a copy: the plan's own answer is the one the source gives. */
    @Test
    void theRewritesTheProofWasAppliedToAreNotChanged() {
        WalkRewrites plans = foldEnteredTwice();

        plans.provingTheSameAt(Set.of(HERE, THERE));

        assertEquals(2, asked(plans));
    }
}
