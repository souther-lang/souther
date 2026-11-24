package souther.compiler.meaning;

/**
 * What a reading comes to for a statement, which asks each statement once ({@link
 * StatementReading}).
 *
 * <p>The only thing the ways down the parts of a statement ({@link Proposition#anyPart} and the
 * others) are handed, so that a reader that goes down them is one that does not pay for every way.
 * Sealed to the two that keep what they come to: a function made on the spot would be one that
 * keeps nothing, and handed to the ways down the parts it would be a reader that pays for every
 * way, which is what this is for.
 *
 * @param <R> what the reading comes to for a statement
 */
public sealed interface EachOnce<R>
        permits StatementReading, StatementReading.InContext.In {

    /** What the reading comes to for {@code stated}. */
    R read(Proposition stated);
}
