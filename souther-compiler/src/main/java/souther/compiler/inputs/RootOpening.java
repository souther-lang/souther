package souther.compiler.inputs;

/**
 * Why a value's rules were opened where they were, which is what says when the positions under them
 * stand.
 *
 * <p>A rule root is a reading opened at a value, and not a fact about every value the behavior
 * takes. What a parameter's rules say holds of every row; what a case's rules say holds of the rows
 * whose value turned out to be that case, and what an element's say holds where the sequence holds
 * one. A reading that met all of them into one space would be saying that every row is every case
 * at once — which is a sum's cases refusing an input between them, and a rule of the value above
 * reaching a position under a name nothing resolves to.
 *
 * <p>Read where the reading is opened and never worked out afterwards from the path. The steps say
 * a narrowing was taken; they do not say which value's rules were being read when it was, and a
 * reader recovering the second from the first would be answering with whichever root it happened to
 * find.
 */
sealed interface RootOpening {

    /** A parameter: the behavior takes it, so its rules hold of every row. */
    record Taken() implements RootOpening {}

    /**
     * A case: its rules hold where the value at {@link SharedNames#sum} turned out to be that case.
     *
     * <p><b>Written for a refinement and not for a sum's case.</b> A sum states its cases and an
     * optional states whether it holds anything, and {@link Refinement} already reads both as
     * narrowings of one kind — so an optional's {@code Some} is one of these rather than a shape
     * that arrives later with nothing to be an instance of.
     *
     * <p><b>Standing under a narrowing and carrying a name across it are two facts.</b> This is
     * written wherever a case is opened, and the crossing it carries names nothing where the cases
     * share nothing. Read as one — a narrowing being recorded only where a name crosses it — the
     * condition a root stands under would go missing at exactly the sums whose cases have nothing
     * in common.
     *
     * @param outer    where the rules the narrowing was taken from were read
     * @param crossing the narrowing, and which of the value above's names reach across it
     */
    record Refined(TermPath outer, SharedNames crossing) implements RootOpening {}

    /**
     * An element: its rules hold where {@code sequence} holds one.
     *
     * <p>Nothing crosses. What a clause of the value out here says is written about the sequence,
     * and an element is a value with a declaration of its own.
     *
     * @param outer    where the rules that were handed on were read
     * @param sequence the container, whose being empty is a row this behavior takes as readily as
     *                 one that fills it
     */
    record Inside(TermPath outer, TermPath sequence) implements RootOpening {}
}
