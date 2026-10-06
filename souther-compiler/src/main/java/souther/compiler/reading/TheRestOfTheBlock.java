package souther.compiler.reading;

import souther.compiler.coverage.ArmProbe;
import souther.compiler.coverage.ComparisonEmissionSite;

import java.util.List;

/**
 * Where a run that got past a {@code guard} went on, and the comparisons the guard decides by.
 *
 * <p>Both of one guard, read off the guard. Which comparison stopped a run at it is one of its own
 * condition's, and asked of anything wider — every comparison the run came out of the false way —
 * a comparison an earlier fork decided by would be taken for the one the guard refused on.
 *
 * <p>Read off the condition and not off a way into the arm. A way in says what holds on the way
 * there in the words a row is composed in, and a comparison of a number no position holds — what
 * a list's elements add up to — has no such words; it is still a comparison of the condition, and
 * still where a run through it is recorded.
 *
 * @param arm       the arm the rest of the block is
 * @param decidedBy where each comparison of the guard's condition is recorded, in the order the
 *                  condition is written; none where nothing records them
 */
public record TheRestOfTheBlock(ArmProbe arm, List<ComparisonEmissionSite> decidedBy) {

    public TheRestOfTheBlock {
        decidedBy = List.copyOf(decidedBy);
    }
}
