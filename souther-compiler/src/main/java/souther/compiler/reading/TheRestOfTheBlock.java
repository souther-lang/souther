package souther.compiler.reading;

import souther.compiler.coverage.ArmProbe;
import souther.compiler.coverage.ControlClaim;

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
 * @param arm  the arm the rest of the block is
 * @param ways each way the condition comes out the way the block goes on, in the order the reading
 *             of the body reached them; none where the reading could not write them all down
 */
public record TheRestOfTheBlock(ArmProbe arm, List<List<ControlClaim>> ways) {

    public TheRestOfTheBlock {
        ways = ways.stream().map(List::copyOf).toList();
    }
}
