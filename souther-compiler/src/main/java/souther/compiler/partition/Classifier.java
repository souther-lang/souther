package souther.compiler.partition;

import souther.compiler.observe.ObservedValue;

import java.util.function.Predicate;

/**
 * Whether a value an {@code example} row was given belongs to one equivalence class.
 *
 * <p>Separate from being able to produce a value of that class. A class can be recognised in rows the
 * author already wrote while nothing can generate a representative for it — a type whose invariant is
 * a pattern, a record whose fields constrain each other — and treating those as unmeasurable would
 * throw away coverage that is already there.
 *
 * <p>The answer is a {@link Membership} and not a {@code boolean} because a classifier may have to
 * read the value before it can say anything about it, and reading can fail. What did the reading
 * says why it failed; nothing downstream is in a position to work it out.
 */
@FunctionalInterface
public interface Classifier {

    Membership membershipOf(ObservedValue value);

    /**
     * One that answers by looking at the value it is given.
     *
     * <p>For the classes told apart by shape — a case of a sum, a {@code Bool}, whether an optional
     * holds anything — where the value at the position is the value to look at. An observation that
     * did not arrive is answered before the predicate is asked, because that is a fact about the
     * observation rather than a thing the class declines.
     */
    static Classifier byShape(Predicate<ObservedValue> holds) {
        return value -> {
            Membership.Incomplete unread = Membership.unread(value);
            return unread != null ? unread : Membership.of(holds.test(value));
        };
    }

    /** Recognises nothing: a class that exists but cannot be told from another by looking. */
    static Classifier none() {
        return _ -> Membership.NO_MATCH;
    }
}
