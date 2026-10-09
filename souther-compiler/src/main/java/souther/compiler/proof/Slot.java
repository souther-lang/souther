package souther.compiler.proof;

import java.util.List;

/**
 * What a statement of what a walk carries names: an argument of the operation, a part of what the
 * walk carries, the part of its list it has walked, or any value at all.
 *
 * <p>The words a lemma's clauses are written in once they are held to the operation they are about
 * ({@code check.OperationFactBinder}). A law is over the arguments alone; what a walk carries is
 * about the walk as well, so it has words of its own.
 */
public sealed interface Slot {

    /** The operation's argument at {@code position}. */
    record Place(int position) implements Slot {}

    /** The part at {@code path} of what the walk carries; the whole of it where the path is
     *  empty. */
    record Carried(List<Integer> path) implements Slot {

        public Carried {
            path = List.copyOf(path);
        }
    }

    /** The part of the walk's list it has walked so far. */
    record Walked() implements Slot {}

    /** Any value at all, the same wherever {@code which} names it in one statement. */
    record Every(int which) implements Slot {}
}
