package souther.compiler.check;

import souther.compiler.core.Core;

/**
 * What the body of a binding is read in.
 *
 * <p>Apart from {@link ClauseReading} because the two answer different questions about one clause. A
 * reading says what a leaf states and how two statements compose; this says what a name means, which
 * is the environment's answer and not the reader's (ADR-0106). Held together, every reading would
 * carry an account of a binder, and three accounts of one thing agree only until somebody changes
 * one of them.
 *
 * <p>So the fold below finds the scope boundary and asks this; no evaluator is handed a binding as
 * the clause's shape. For a reading carrying {@link Denotations} the answer is {@link Terms#inside},
 * which is the one place a {@code let} is entered.
 *
 * <p><b>A binding nested inside a leaf is still part of that leaf</b>, and this is not where it is
 * crossed. What crosses it there is each question the leaf language asks about its own inside —
 * which position an operand is, what written value it is, which positions a part names — and each
 * of those asks the environment rather than working the binder out. A question there that answers
 * from the tree alone is one this decision has not reached (ADR-0106).
 *
 * @param <E> what a reading carries as it goes inside a binding
 */
@FunctionalInterface
interface ClauseScope<E> {

    /** What {@code li}'s body is read in, given what stood outside it. */
    E inside(Core.LetIn li, E outside);

    /**
     * The scope of a reading that carries nothing, for which a binding changes nothing.
     *
     * <p>Not "a binding this one cannot enter". A reading whose state is a count has no environment
     * to enter it in, so the body is read as it stands and the answer is exact.
     */
    static <E> ClauseScope<E> unchanged() {
        return (_, outside) -> outside;
    }
}
