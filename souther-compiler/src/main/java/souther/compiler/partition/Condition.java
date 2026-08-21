package souther.compiler.partition;

import souther.compiler.ast.Hir;
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
 * <p>What is not here is which comparisons appear <em>anywhere</em> in a condition — inside an
 * argument to a call, under an operator this does not read. That is a different question, asked of
 * the whole subtree rather than of the condition's structure, and it is answered where it is asked
 * ({@code GuardThresholds.compared}). Reading one for the other is how a comparison nothing could
 * turn into a line would come back as a line.
 */
sealed interface Condition {

    /** Both, and the right one runs only where the left held. */
    record Both(Condition left, Condition right) implements Condition {}

    /** Either, and the right one runs only where the left did not hold. */
    record Either(Condition left, Condition right) implements Condition {}

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
        if (e instanceof Core.Binary binary && combines(binary.op())) {
            Condition left = of(binary.left(), reads);
            Condition right = of(binary.right(), reads);
            return binary.op() == Hir.BinOp.AND ? new Both(left, right) : new Either(left, right);
        }
        if (e instanceof Core.Binary comparison) {
            return new Compares(comparison, reads);
        }
        return new NotRead(e);
    }

    /** Whether an operator joins two conditions rather than comparing two values. */
    static boolean combines(Hir.BinOp op) {
        return op == Hir.BinOp.AND || op == Hir.BinOp.OR;
    }
}
