package souther.compiler.meaning;

/**
 * What a reading comes to for a statement, which asks each statement once ({@link
 * StatementReading}).
 *
 * <p>The only thing the ways down the parts of a statement ({@link Proposition#anyPart} and the
 * others) are handed, so that a reader that goes down them is one that does not pay for every way.
 *
 * @param <R> what the reading comes to for a statement
 */
@FunctionalInterface
public interface EachOnce<R> {

    /** What the reading comes to for {@code stated}. */
    R read(Proposition stated);
}
