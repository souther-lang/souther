package souther.compiler.meaning;

import souther.compiler.collect.EachNodeOnce;

/**
 * A reading that goes down the parts of statements, asked of each statement once.
 *
 * <p>A condition read through a name used twice is held by two statements, so the statements are a
 * graph, and the ways down a chain of names each using the one before it twice are two to its
 * length. A reader that recurses into the parts for itself pays for every way. Made here, a reading
 * answers each statement it meets once and hands that answer to every statement above it, so what
 * it costs is the statements and not the ways down to them.
 *
 * <p>The only way down the parts of a statement ({@link Proposition#anyPart},
 * {@link Proposition#everyPart}, {@link Proposition#eachPart}, {@link Proposition#sumOverParts})
 * is handed one of these, so a reader that goes down them is one of these. It is made for one
 * question and let go: what it keeps is what that reading came to under the premises it was
 * asked with, and a reading under other premises is a reading of its own.
 *
 * <p>A reading that has an effect — one that gathers what it meets into a collection — has it once
 * for each statement, which is what gathering is: it adds what a statement says to a set, and a
 * statement met by two ways says it once. A reading whose answer for a statement is not the same
 * wherever it stands is not one of these; it goes down the way its owner walks it.
 *
 * <p>Statements are told apart by identity ({@link EachNodeOnce}). Equal statements made apart are
 * two here; those made through {@link Proposition#all} and {@link Proposition#any} are the one kept
 * ({@link SharedPropositions}), which is where a graph of them comes from.
 *
 * <p>Not thread-safe: a reading is one thread's.
 *
 * @param <R> what the reading comes to for a statement
 */
public final class StatementReading<R> {

    /** What a reading comes to for one statement, and how it goes on into its parts. */
    @FunctionalInterface
    public interface At<R> {

        /**
         * What the reading comes to for {@code stated}. Its parts are read through {@code again},
         * which has the answer already for each one asked before.
         */
        R of(Proposition stated, StatementReading<R> again);
    }

    private final At<R> at;

    private final EachNodeOnce<Proposition, R> worked = new EachNodeOnce<>();

    private StatementReading(At<R> at) {
        this.at = at;
    }

    /** A reading that comes to what {@code at} says for each statement it is asked of. */
    public static <R> StatementReading<R> over(At<R> at) {
        return new StatementReading<>(at);
    }

    /** What the reading comes to for {@code stated}, worked out the first time it is asked. */
    public R read(Proposition stated) {
        return worked.of(stated, each -> at.of(each, this));
    }
}
