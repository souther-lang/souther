package souther.compiler.semantics;

/**
 * What the piece an operation makes of one element of a list is, in terms of what its closure
 * answers on that element ({@link OperationFact.AssemblesPieces}).
 */
public enum PieceOfAnElement {

    /** The closure's answer on the element, alone: {@code [f(x)]}. */
    THE_CLOSURES_ANSWER,

    /** The element itself where the closure holds of it, and nothing where it does not:
     *  {@code if keep(x) then [x] else []}. */
    THE_ELEMENT_WHERE_IT_HOLDS,

    /** Every element of the list the closure answers on it: {@code f(x)}. */
    WHAT_THE_CLOSURE_ANSWERS
}
