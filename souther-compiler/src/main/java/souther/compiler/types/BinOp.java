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
 */
public enum BinOp {
    EQ, NE, LT, LE, GT, GE, AND, OR, ADD, SUB, MUL, DIV, CONCAT;

    /**
     * Whether this settles a comparison, which is the one place that says so.
     *
     * <p>Read by everything that has to tell a comparison from what is written the same way.
     * {@code &&} and {@code ||} put comparisons together rather than being ones; the arithmetic
     * operators answer a number. Each reader used to spell the membership out for itself — one
     * as "not {@code &&} or {@code ||}", one as "places something on an order" — and two
     * spellings of one set are two sets an operator added later can land in differently.
     */
    public boolean compares() {
        return switch (this) {
            case EQ, NE, LT, LE, GT, GE -> true;
            case AND, OR, ADD, SUB, MUL, DIV, CONCAT -> false;
        };
    }

    /**
     * Whether this stops as soon as its answer is settled, so that its right operand runs on some
     * runs and not others (spec §a-condition-stops-when-its-answer-is-settled).
     *
     * <p>Here for the reason {@link #compares} is here. Which operands run is part of what the
     * operator means, and every reader that has to know it was spelling the membership out again —
     * a reading of what arrives, a reading of what an expression evaluates, a reading of what a row
     * interacts with. Three spellings of one set are three sets an operator added later can land in
     * differently.
     */
    public boolean stopsWhenItsAnswerIsSettled() {
        return switch (this) {
            case AND, OR -> true;
            case EQ, NE, LT, LE, GT, GE, ADD, SUB, MUL, DIV, CONCAT -> false;
        };
    }
}
