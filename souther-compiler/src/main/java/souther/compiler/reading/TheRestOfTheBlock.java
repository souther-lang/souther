package souther.compiler.reading;

import souther.compiler.coverage.ArmProbe;
import souther.compiler.coverage.ControlClaim;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.coverage.SourceOutcome;
import souther.compiler.types.SourceConstruct;

import java.util.List;

/**
 * Where a run that got past a {@code guard} went on, and each way the guard's condition lets it.
 *
 * <p>Both of one guard, read off the guard. What stopped a run at it is its own condition, and asked
 * of anything wider — every comparison the run came out of the false way — a comparison an earlier
 * fork decided by would be taken for the one the guard refused on.
 *
 * <p>Each way as what a run that took it would be seen doing, which is a comparison coming out a
 * way and not merely a comparison: under {@code Bool.not(x <= 0)} the run goes on where
 * {@code x <= 0} came out false. A way is a conjunction, every claim of it at once, and the ways
 * are the alternatives — under {@code a > 0 || b > 0} either is a way on.
 *
 * <p>Not the way into the arm. A way in says what holds on the way there in the words a row is
 * composed in, and is listed only where every way is known to be one the body has; a comparison of
 * a number no position holds — what a list's elements add up to — leaves the arm with none. These
 * are each way that may be there, which a reader that runs the row it composes can check.
 *
 * <p>And the guard as the arm a run that did not get past it leaves by, which is what a report
 * says a row stopped at. Held here rather than found again from the probe, because the walk that
 * read the guard had the site in hand, and a reader that looked it up a second time would be a
 * second answer to which guard this is.
 *
 * @param refused the arm by which a run leaves the guard refused
 * @param arm     the arm the rest of the block is
 * @param ways    each way the condition comes out the way the block goes on, in the order the
 *                reading of the body reached them; none where the reading could not write them
 *                all down
 */
public record TheRestOfTheBlock(CoverageSites.ArmSite refused, ArmProbe arm,
                                List<List<ControlClaim>> ways) {

    public TheRestOfTheBlock {
        if (refused.construct() != SourceConstruct.GUARD
                || !(refused.outcome() instanceof SourceOutcome.Failed)) {
            throw new IllegalArgumentException(
                    "the rest of a block is past a guard, and what a run that did not get there"
                            + " leaves by is the guard refusing it: " + refused);
        }
        ways = ways.stream().map(List::copyOf).toList();
    }
}
