package souther.compiler.types;

/**
 * A binary operator of the language.
 *
 * <p>Here rather than in a tree, because two of them write it: the resolved tree a check reads, and
 * the Core that check produces for a backend. Neither decides what the operator is — {@code <}
 * places a value on an order whichever tree is being read — so an operator owned by one of them
 * would make the other's reading of it a translation. Core reaching into the resolved tree for the
 * operator is what put {@code souther.compiler.ast} on the boundary a backend outside this compiler
 * reads.
 *
 * <p>The parsed tree keeps its own, which is what the parser produced before anything was resolved.
 *
 * <p><b>What is answered here is what an operator is on its own.</b> Which family it belongs to and
 * which of its operands run are settled by the operator and by nothing else — not by the types it
 * was written between, not by the polarity it is read under, not by which phase is reading. A
 * reader that works either out for itself is a second answer to one question, and two answers to
 * one question are two questions an operator added later can be given different answers to.
 *
 * <p><b>And what a phase does with one is that phase's.</b> How an operator is elaborated,
 * evaluated as a constant or emitted is a decision about the phase and not about the operator, so
 * it stays where it is made and is exhaustive there. An operator added to the language is then
 * classified once, here, and decided about once in each phase that has to do something with it.
 */
public enum BinOp {
    EQ(Family.COMPARISON),
    NE(Family.COMPARISON),
    LT(Family.COMPARISON),
    LE(Family.COMPARISON),
    GT(Family.COMPARISON),
    GE(Family.COMPARISON),

    AND(Family.CONDITION_COMBINATION),
    OR(Family.CONDITION_COMBINATION),

    ADD(Family.ARITHMETIC),
    SUB(Family.ARITHMETIC),
    MUL(Family.ARITHMETIC),
    DIV(Family.ARITHMETIC),

    CONCAT(Family.CONCATENATION);

    /**
     * What an operator does with the two values it stands between.
     *
     * <p>Given where the constant is declared, so a constant cannot be written without saying which
     * of these it is, and the memberships below cannot disagree: an operator is in exactly one
     * family, and each question about which operators are which is that one classification read
     * another way.
     *
     * <p><b>Private, because a partition is not a vocabulary.</b> A reader asks the question it has,
     * and hands on what it established rather than the family it established it from.
     *
     * <p>{@link #CONCATENATION} is here for the same reason the others are, though nothing asks for
     * it by name yet. Left out, joining two sequences would be what is left over from three sets
     * rather than a family somebody declared, and an operator arriving later could be left over
     * from four.
     */
    private enum Family {
        COMPARISON,
        CONDITION_COMBINATION,
        ARITHMETIC,
        CONCATENATION
    }

    private final Family family;

    BinOp(Family family) {
        this.family = family;
    }

    /** Whether this settles a comparison, which is what everything that has to tell one from what
     *  is written the same way reads. */
    public boolean compares() {
        return family == Family.COMPARISON;
    }

    /** Whether this answers a number of its two operands. */
    public boolean answersANumber() {
        return family == Family.ARITHMETIC;
    }

    /** Whether this puts two conditions together rather than being one. */
    public boolean joinsTwoConditions() {
        return family == Family.CONDITION_COMBINATION;
    }

    /**
     * Which way the left operand has to come out for the right one to run, or null where both
     * always run (spec §a-condition-stops-when-its-answer-is-settled).
     *
     * <p>Here for the reason the family is here, and beside it rather than out of it: which
     * operands run is part of what the operator means, and a reader that works it out for itself is
     * a second rule an operator added later can land in differently. It is not read off the family.
     * {@code &&} and {@code ||} are the two that join conditions and the two that stop early, and
     * those are one set answering two questions rather than one question — an operator joining two
     * conditions without stopping early would part them, and a reader taking either answer for the
     * other would be reading a decision nobody made.
     *
     * <p>The polarity and not the membership, because the membership follows from it and the
     * polarity does not follow from anything. Answered as "which operators stop early", a reader is
     * left to work out which way for itself, and the answer it arrives at — the right side is
     * reached having held — is right only while {@code ||} is the only other one.
     */
    public Boolean rightRunsWhenLeftIs() {
        return switch (this) {
            case AND -> Boolean.TRUE;
            case OR -> Boolean.FALSE;
            case EQ, NE, LT, LE, GT, GE, ADD, SUB, MUL, DIV, CONCAT -> null;
        };
    }

    /** Whether this stops as soon as its answer is settled, so that its right operand runs on some
     * runs and not others. What decides it is {@link #rightRunsWhenLeftIs}: an operator that names
     * a way for its right to run is one that has runs where it does not. */
    public boolean stopsWhenItsAnswerIsSettled() {
        return rightRunsWhenLeftIs() != null;
    }
}
