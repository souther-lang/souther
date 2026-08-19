package souther.compiler.partition;

import souther.compiler.ast.Hir;
import souther.compiler.check.AffineForms;
import souther.compiler.check.Carrier;
import souther.compiler.check.ComparisonClaim;
import souther.compiler.check.Location;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.NumericDomain.LinearForm;

import java.math.BigDecimal;
import java.util.Map;

/**
 * A comparison read as one statement: {@code Σ coef·position REL threshold}.
 *
 * <p><b>What a rule says, and not how it was written.</b> {@code a + 1 <= 10}, {@code 2 * a <= 10}
 * and {@code a <= b - 1} were each a comparison the measure could not read, because the readers
 * before this one wanted a bare position on one side and a written value or a bare position on the
 * other. What decides which quantity a rule cuts is this form and never the spelling, so
 * {@code a > b}, {@code a + 0 > b} and {@code a > b + 0} are one rule about one quantity.
 *
 * <p>The constant is moved to the threshold rather than kept in the quantity. {@code a + 1 <= 10} is
 * {@code a <= 9} and {@code 2 * a <= 9} is {@code 2 * a <= 9}, so a quantity is constant-free and a
 * threshold is a number. Left in the quantity, the values {@code 2 * a} takes would be the even
 * numbers under one spelling and the odd ones shifted by nine under another, and the two would
 * disagree about where the border's points are.
 *
 * <p>The arithmetic is {@link AffineForms}'s, which is the walk the discharge check reads a clause
 * with. The atoms are this side's: a position of a behavior's input, or a count taken of one.
 *
 * @param form  the quantity, with no constant in it
 * @param cut   where the rule cuts it
 * @param claim what the operator states about the threshold's own value
 */
record AffineReading(LinearForm<NumericTerm> form, BigDecimal cut, ComparisonClaim claim) {

    /**
     * {@code comparison} as this form, or null where nothing here reads it.
     *
     * <p>Null where the arithmetic names no position, where an operand is outside the affine
     * fragment, and where the comparison places nothing — an operand of a variable product is one
     * value and the rule about it is one this does not model.
     */
    static AffineReading of(Core.Binary comparison, InputReads reads, Symbols symbols) {
        if (ComparisonClaim.of(comparison.op()) instanceof ComparisonClaim.Nothing) {
            return null;
        }
        LinearForm<NumericTerm> left = affine(comparison.left(), reads, symbols);
        LinearForm<NumericTerm> right = affine(comparison.right(), reads, symbols);
        if (left == null || right == null) {
            return null;
        }
        LinearForm<NumericTerm> whole = left.minus(right);
        if (whole.coefs().isEmpty()) {
            return null;   // a comparison of constants states nothing about any position
        }
        return new AffineReading(new LinearForm<>(BigDecimal.ZERO, whole.coefs()),
                whole.constant().negate(), ComparisonClaim.of(comparison.op()));
    }

    /** {@code e} as an affine form over the behavior's positions, or null where it is not one. */
    static LinearForm<NumericTerm> affine(Core e, InputReads reads, Symbols symbols) {
        return AffineForms.of(e, reads, new AffineForms.Leaves<NumericTerm, InputReads>() {

            @Override
            public LinearForm<NumericTerm> leafOf(Core node, InputReads at) {
                NumericTerm term = GuardThresholds.termOf(node, at, symbols);
                return term == null ? null : LinearForm.atom(term);
            }

            @Override
            public InputReads inside(Core.LetIn li, InputReads at) {
                return at.and(li.binder(), li.value());
            }

            @Override
            public boolean readsThrough(Core.FieldAccess fa, InputReads at) {
                return at.pathOf(fa.target(), symbols) == null
                        && !Location.isStep(fa.target().type(), fa.field(), symbols);
            }
        });
    }

    /** The one position this cuts where it cuts one with a coefficient of one, or null. Read after
     *  {@link #mirrored()}, so a form written {@code -x} is one written {@code x} against the
     *  opposite threshold. */
    NumericTerm oneCoordinate() {
        if (form.coefs().size() != 1) {
            return null;
        }
        Map.Entry<NumericTerm, BigDecimal> only = form.coefs().entrySet().iterator().next();
        return only.getValue().compareTo(BigDecimal.ONE) == 0 ? only.getKey() : null;
    }

    /**
     * The two positions this holds apart, as {@code on} and {@code against}, or null where it holds
     * no two apart.
     *
     * <p>Coefficients of one and minus one, which is what makes the quantity a distance: {@code 2a -
     * b} is not how far two positions stand apart, it is an arithmetic form over both of them.
     */
    NumericTerm[] twoCoordinates() {
        if (form.coefs().size() != 2) {
            return null;
        }
        NumericTerm on = null;
        NumericTerm against = null;
        for (Map.Entry<NumericTerm, BigDecimal> each : form.coefs().entrySet()) {
            if (each.getValue().compareTo(BigDecimal.ONE) == 0) {
                on = each.getKey();
            } else if (each.getValue().compareTo(BigDecimal.ONE.negate()) == 0) {
                against = each.getKey();
            }
        }
        return on == null || against == null ? null : new NumericTerm[] {on, against};
    }

    /**
     * The same statement with the quantity negated and the threshold and operator turned round.
     *
     * <p>{@code -x <= -5} states what {@code x >= 5} states. Which of the two a reading meets is
     * whichever way the author wrote the subtraction, and it is not a difference between two rules.
     */
    AffineReading mirrored() {
        return new AffineReading(form.negate(), cut.negate(), turned(claim));
    }

    /** Whether the quantity is written with every coefficient negative, which is the same statement
     *  turned round. */
    boolean facesTheOtherWay() {
        return form.coefs().values().stream().allMatch(c -> c.signum() < 0);
    }

    /** What the operator states once both sides are turned round. */
    private static ComparisonClaim turned(ComparisonClaim claim) {
        return switch (claim) {
            // Turning the sides round moves the threshold's own value to the other class and leaves
            // whether the rule holds there alone: `x <= c` and `-x >= -c` are one statement.
            case ComparisonClaim.Cut cut ->
                    new ComparisonClaim.Cut(!cut.valueBelongsBelow(), cut.holdsAtTheValue());
            // An equality names a value and orders nothing, so there is nothing to turn round.
            case ComparisonClaim.Singled singled -> singled;
            case ComparisonClaim.Nothing nothing -> nothing;
        };
    }

    /** The order this form's positions are counted on, or null where they are not all on one. */
    Carrier carrier(Symbols symbols, java.util.function.Function<NumericTerm, Carrier> of) {
        Carrier one = null;
        for (NumericTerm term : form.coefs().keySet()) {
            Carrier here = of.apply(term);
            if (here == null || (one != null && !one.equals(here))) {
                return null;
            }
            one = here;
        }
        return one;
    }

    /** Whether the operator orders the values around the threshold rather than singling one out. */
    boolean orders() {
        return claim instanceof ComparisonClaim.Cut;
    }

    /** Whether an operator is one this reads at all. */
    static boolean places(Hir.BinOp op) {
        return ComparisonClaim.places(op);
    }
}
