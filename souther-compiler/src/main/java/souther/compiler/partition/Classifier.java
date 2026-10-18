package souther.compiler.partition;

import souther.compiler.inputs.Membership;
import souther.compiler.observe.ObservedValue;

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
 *
 * <p><b>A way of asking, and never what a class is.</b> What a class means is a {@link Recognition},
 * which is a value; one of these is made from one of those by {@link Recognitions#reading}, wherever
 * something is about to read a row. Nothing builds one any other way — a class whose meaning existed
 * only inside a function it had been handed could not be compared with another class and could not
 * be kept in an answer.
 */
@FunctionalInterface
public interface Classifier {

    Membership membershipOf(ObservedValue value);
}
