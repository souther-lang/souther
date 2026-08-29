package souther.compiler.coverage;

/**
 * One fork of a body, as the thing its arms are arms of.
 *
 * <p>What tells two decisions apart where all a reading can say is which fork they are of. A reading
 * that cannot name the position a fork is about still knows that going one way and going the other
 * are the same decision settled twice, and that is what this is for.
 *
 * <p>Named by the first of its arms, and minted where the arms are. The two are made in one act, so
 * nothing looks a fork up afterwards from a number it was handed: an identity found again from a
 * component is an identity two readers can derive differently, which is what a number standing in
 * for a place already did once here.
 *
 * <p>Occurrence and not fork: a non-recursive helper is spliced into each body that calls it, so one
 * {@code if} the author wrote is several of these, each reached under its caller's own conditions.
 */
public record ForkOccurrence(int controlId) {

    @Override
    public String toString() {
        return "fork " + controlId;
    }
}
