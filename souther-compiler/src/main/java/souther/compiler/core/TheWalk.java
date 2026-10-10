package souther.compiler.core;

import souther.compiler.types.ValueName;

/**
 * The library's one loop, as its body says it is: where each of its arguments is, and that what it
 * does is walk a list from an index.
 *
 * <p>Read off the body while the library is built, and not written down. A call of it answers the
 * seed where the container holds nothing at the index, and otherwise the walk from the next index
 * with the seed replaced by the step applied to it and the element there. That is what a reader of
 * a fold, an output lowering one as a loop and the check that a recursion ends may each assume of
 * it, and the only thing.
 *
 * @param operation   the walk
 * @param step        the argument holding the step
 * @param seed        the argument holding what the walk starts from, which it answers at the end
 * @param container   the argument holding the list it walks
 * @param index       the argument holding the index it walks from
 * @param accumulator the step's parameter the value carried so far arrives on
 * @param element     the step's parameter the element at the index arrives on
 * @param reads       what the walk reads the element at its index with, handed the index first and
 *                    the list second
 */
public record TheWalk(ValueName.Stdlib.Operation operation, int step, int seed, int container,
                      int index, int accumulator, int element, ValueName.Stdlib.Operation reads) {

    /**
     * Whether the walk takes its arguments where an output's loop reads them — step, seed, list,
     * index — and hands its step what it carries and then the element.
     *
     * <p>An output emits a walk from the head of a list as a loop of its own, written against one
     * order of arguments. A walk taking them in another is not that loop, and is emitted as the
     * call it is.
     */
    public boolean inTheLoopsOrder() {
        return step == 0 && seed == 1 && container == 2 && index == 3 && accumulator == 0
                && element == 1;
    }
}
