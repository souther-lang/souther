package souther.compiler.partition;

import souther.compiler.types.BinOp;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputReads;

/**
 * What a condition of a body is made of.
 *
 * <p><b>One reading, because three readers were each making their own.</b> Which comparisons a fork
 * turns on, what each of them stands under, and what an arm proves are three questions about one
 * structure — and each was answered by matching on the shape of the {@link Core} node in front of
 * it. So each knew, on its own, which shapes are transparent, which combine, which are something to
 * say about, and which are where this compiler stops. A shape one of them learned to see through was
 * a shape the others still could not.
 *
 * <p>They came apart where a helper is called in a condition. An expanded helper binds the call's
 * argument to its own parameter, so what stands in the condition is a binding around the comparison
 * rather than the comparison — and the reading that finds comparisons anywhere in a condition saw it
 * and reported it as a rule written in a form this compiler does not read, while the reading that
 * draws lines never reached it at all. One line went missing, the position it divides came back
 * divided no way, and the region a guard beside it is searched in lost what that comparison
 * establishes. All from moving a comparison into a {@code let}, which changes nothing about what the
 * model says.
 *
 * <p>So the vocabulary is here and the readers fold over it. Four shapes:
 *
 * <ul>
 *   <li>{@link Both} and {@link Either} — the two operators a condition is built from, each of
 *       which stops as soon as it is settled;
 *   <li>{@link Compares} — one comparison, with the reading of the names in force where it stands;
 *   <li>{@link NotRead} — where this stops. A condition can be anything a {@code Bool} is, and what
 *       is not one of the shapes above says nothing here rather than being guessed at.
 * </ul>
 *
 * <p><b>A binding is transparent and is not one of the shapes.</b> What a {@code let} contributes is
 * where the names in its body point, which is why {@link Compares} carries the reading rather than
 * every reader threading one alongside. Carried as a shape instead, each reader would have to know
 * to look through it, which is the arrangement this replaces.
 *
 * <p><b>Not a way of finding comparisons.</b> This says what a boolean subtree means, and it used to
 * be walked to visit the comparisons inside one as well. A walk of a subtree needs a root, the root
 * anything ever gave it was a fork's condition, and so what a row had satisfied on the way to a
 * comparison was established only where a fork was written — {@code A && B} said nothing about
 * {@code B} where {@code if A then B else false} did. Which comparisons a body holds is
 * {@link souther.compiler.coverage.ComparisonCatalog}'s and where each of them stands is
 * {@link ComparisonReadings}'s, and neither has a root to be given.
 */
sealed interface Condition {

    /**
     * The node this is a reading of.
     *
     * <p>Kept by every shape, because a reader that could not take one in owes the place it is
     * written. Recovered afterwards from what is under a node, the place would be a child's — a
     * conjunction nothing could turn into a region would be reported at whichever operand happened
     * to be first, which is a second account of where a condition stands and is the kind of thing
     * this vocabulary exists to have one of.
     */
    Core at();

    /** Both, and the right one runs only where the left held. */
    record Both(Core.Binary at, Condition left, Condition right) implements Condition {}

    /** Either, and the right one runs only where the left did not hold. */
    record Either(Core.Binary at, Condition left, Condition right) implements Condition {}

    /**
     * One comparison, and where the names in it point.
     *
     * @param reads the reading in force where this comparison stands, which is the outer one with
     *              every binding between here and the top taken in. A comparison inside an expanded
     *              helper is about the argument the call handed it, and read against the outer names
     *              it is about nothing
     */
    record Compares(Core.Binary at, InputReads reads) implements Condition {}

    /** Where this reading stops: a condition of a shape it has no words for. */
    record NotRead(Core at) implements Condition {}

    /**
     * {@code e} read as a condition, under {@code reads}.
     *
     * <p>Bindings are looked through and their names taken in; the two operators are taken apart;
     * everything else is either one comparison or nowhere this reading goes.
     */
    static Condition of(Core e, InputReads reads) {
        if (e instanceof Core.LetIn let) {
            return of(let.body(), reads.and(let.binder(), let.value()));
        }
        // A name standing for a truth is that truth. What a `let` binds is already carried for the
        // sake of which position a term names, and stopping at the name here left a fork on one
        // proving nothing while the same condition written out proved a comparison — the reading
        // being transparent to one reader and opaque to the other, over one binding.
        //
        // It terminates because a binder's value can only mention binders introduced before it, so
        // each step of this goes strictly outwards.
        if (e instanceof Core.Read name && name.binding() != null) {
            Core bound = reads.bound().get(name.binding());
            if (bound != null) {
                return of(bound, reads);
            }
        }
        if (e instanceof Core.Binary binary && combines(binary.op())) {
            Condition left = of(binary.left(), reads);
            Condition right = of(binary.right(), reads);
            return binary.op() == BinOp.AND
                    ? new Both(binary, left, right) : new Either(binary, left, right);
        }
        if (e instanceof Core.Binary comparison && comparison.op().compares()) {
            return new Compares(comparison, reads);
        }
        return new NotRead(e);
    }

    /** Whether an operator joins two conditions rather than comparing two values. */
    static boolean combines(BinOp op) {
        return op == BinOp.AND || op == BinOp.OR;
    }

    // Which operators compare is `BinOp#compares` and is asked rather than spelled out again.
    // Written here as "a binary that is not `&&` or `||`", this said arithmetic was a comparison —
    // which nothing in a condition is, so it was a spelling that happened to be right.
}
