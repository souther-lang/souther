package souther.compiler.check;

import souther.compiler.ast.Hir;

import java.math.BigDecimal;

/**
 * The number a literal an author wrote names.
 *
 * <p>What is here is the reading of a written figure and nothing else: an integer, a decimal, and a
 * negation of either. No carrier is asked, no rule is read, and nothing about where a value stops
 * or what the rules leave is in it. So a reader working out what a clause states may have this, and
 * having it says nothing about whether anything answered the clause.
 *
 * <p><b>Its own type, and not {@link InvariantBound}'s.</b> That one reads a rule into where an end
 * was placed, which is an answer about the model, and this was declared inside it. A classification
 * of a clause has to know what {@code 5.00m} is a number of — the carrier asks that of every
 * literal it meets ({@link Carrier#literalOf}) — so a check reading which types a classification
 * depends on found it depending on a reader of ends. The dependency was on these two functions and
 * on nothing else of that type, which is what makes this a misplacement rather than a real edge.
 */
public final class NumericLiterals {

    private NumericLiterals() {}

    /**
     * A whole number a literal names, or null where it names one with a fraction.
     *
     * <p>A value that steps one at a time is not bounded at a place between two of its values.
     */
    public static BigDecimal wholeLiteralOf(Hir.Expr e) {
        BigDecimal read = literalOf(e);
        return read == null || read.stripTrailingZeros().scale() > 0 ? null : read;
    }

    /** A numeric literal, negation included. A bare integer counts against a decimal, since a
     *  literal takes the other side's type. */
    public static BigDecimal literalOf(Hir.Expr e) {
        return switch (e) {
            case Hir.IntLit lit -> BigDecimal.valueOf(lit.value());
            case Hir.DecimalLit lit -> normalized(lit.value());
            case Hir.Neg neg -> negated(literalOf(neg.operand()));
            case null, default -> null;
        };
    }

    /**
     * The number a literal names, without how many places it was written to.
     *
     * <p>{@code 5.0m} and {@code 5.00m} are one constraint, so they have to reach a range as one
     * number: two spellings of an end would be two lines through a position, both holding the same
     * values, and one boundary owed twice under one printed figure. Trailing zeros left of the point
     * are put back, so a hundred is written as one.
     */
    private static BigDecimal normalized(BigDecimal value) {
        BigDecimal bare = value.stripTrailingZeros();
        return bare.scale() < 0 ? bare.setScale(0) : bare;
    }

    private static BigDecimal negated(BigDecimal value) {
        return value == null ? null : value.negate();
    }
}
