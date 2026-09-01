package souther.compiler.semantics;

import souther.compiler.types.BinOp;

import java.util.Optional;

/**
 * What a connective makes of the two conditions it stands between.
 *
 * <p>The answer a reader takes away from recognising a connective. Recognition answered as a
 * membership says that two conditions were joined and not which way, so what a reader held
 * afterwards was the operator, and it read the operator again where the meaning was wanted. The
 * rule that a stated conjunction gives both halves and a denied disjunction gives both halves was
 * then written out at each of those places, and each of them could be taught a different one.
 *
 * <p><b>What a denial does is here and not in any of them.</b> Denying a condition exchanges the
 * two answers, which is the whole of what a denial does to a connective, and a reader carrying a
 * polarity asks for the answer under it rather than working the exchange out beside the operator.
 *
 * <p>Nothing here is about how the two halves run. Which operand runs when is
 * {@link BinOp#rightRunsWhenLeftIs}, and the two questions are told apart by the same two operators
 * today — a connective composing without stopping early would part them, and reading either answer
 * off the other is a coupling between facts that do not decide each other.
 */
public enum ConditionJoin {

    /** Both of the halves. */
    BOTH,

    /** One of the halves, or both of them. */
    EITHER;

    /**
     * What {@code op} composes where it is stated, which is nothing where it joins no two
     * conditions.
     *
     * <p>Which operators join two conditions is {@link BinOp#joinsTwoConditions}'s answer and this
     * asks it rather than listing them again. Two lists can be given different answers about one
     * operator added later, and a reader would then be told that something states a composition
     * where the language says it is not a connective at all.
     */
    public static Optional<ConditionJoin> of(BinOp op) {
        if (!op.joinsTwoConditions()) {
            return Optional.empty();
        }
        return switch (op) {
            case AND -> Optional.of(BOTH);
            case OR -> Optional.of(EITHER);
            // Refused above and written out here so the switch stays exhaustive: an operator added
            // to the language stops the compile here and is decided about rather than falling in.
            // The arms answer the absence the refusal above answered, and are no second say in
            // which operators join two conditions.
            case EQ, NE, LT, LE, GT, GE, ADD, SUB, MUL, DIV, CONCAT -> Optional.empty();
        };
    }

    /** What the connective composes where the condition it joins is denied: both halves where
     *  either of them would have done, and either of them where both would have. */
    public ConditionJoin denied() {
        return switch (this) {
            case BOTH -> EITHER;
            case EITHER -> BOTH;
        };
    }

    /** What the connective composes where the condition it joins is stated with polarity
     *  {@code positive}, which is what it composes denied where it is not. */
    public ConditionJoin under(boolean positive) {
        return positive ? this : denied();
    }
}
