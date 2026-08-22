package souther.compiler.partition;

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
        if (!comparison.op().compares()) {
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
        AffineReading read = new AffineReading(new LinearForm<>(BigDecimal.ZERO, whole.coefs()),
                whole.constant().negate(), ComparisonClaim.of(comparison.op()));
        // Turned round here and nowhere else. `48 >= 3a + 6b` and `3a + 6b <= 48` are one rule, and
        // a reader that met the first without turning it round drew its border on `-3a - 6b` — the
        // same four points under a name no author wrote, and a different line from the rule written
        // the other way.
        return read.facesTheOtherWay(subjectOf(comparison, left, reads, symbols))
                ? read.mirrored() : read;
    }

    /**
     * The order a form's positions are named in, which settles what "the first coefficient" means.
     *
     * <p>By the position's own name, because that is the one thing about a form that does not depend
     * on how it was written. A form is a map; the order its coefficients were recorded in is the
     * order the author happened to add them in, and a report is a document compared against the one
     * written last time.
     */
    static java.util.List<Map.Entry<NumericTerm, BigDecimal>> ordered(
            LinearForm<NumericTerm> form) {
        return form.coefs().entrySet().stream()
                .sorted(java.util.Comparator.comparing(each -> each.getKey().toString())).toList();
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

    /** The one position this cuts where it cuts one with a coefficient of one, or null. A form
     *  written {@code -x} has already been turned round by {@link #of}, so this asks about the
     *  coefficient as the canonical form has it. */
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
    private AffineReading mirrored() {
        return new AffineReading(form.negate(), cut.negate(), turned(claim));
    }

    /**
     * Whether this is the same statement written the other way round.
     *
     * <p>Which way a statement faces is the sign of one coefficient, and which coefficient is the
     * question. Where the comparison's left side names a position, that one: {@code charge > ceiling}
     * and {@code 3a - 6b <= 48} are lines about what the author put on the left, and deriving the
     * subject where the source states it would rename half the borders in a report. Where it names
     * none — {@code 48 >= 3a - 6b} — nothing is being kept, and the form's own order settles it.
     *
     * <p>Total either way, which is what makes it canonical. Settled by every coefficient being
     * negative, {@code 48 >= 3a - 6b} faced neither way and kept the quantity {@code -3a + 6b} —
     * the same line as {@code 3a - 6b <= 48} under a name no author wrote.
     */
    private boolean facesTheOtherWay(NumericTerm subject) {
        BigDecimal first = subject == null ? null : form.coefs().get(subject);
        return (first != null ? first : ordered(form).getFirst().getValue()).signum() < 0;
    }

    /** The position the comparison's left side names first, or null where it names none. Handed the
     *  reading of that side rather than walking it again: one comparison is read once. */
    private static NumericTerm subjectOf(Core.Binary comparison, LinearForm<NumericTerm> left,
                                         InputReads reads, Symbols symbols) {
        if (left == null || left.coefs().isEmpty()) {
            return null;
        }
        for (souther.compiler.inputs.TermPath named
                : GuardThresholds.mentionedIn(comparison.left(), reads, symbols)) {
            for (NumericTerm atom : left.coefs().keySet()) {
                if (atom.path().equals(named)) {
                    return atom;
                }
            }
        }
        return null;
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

    /**
     * The order this form's positions are counted on, or null where they are not all on one.
     *
     * <p>Asked of each position and not of the operand it was written beside. A form adds its
     * positions together, and two orders whose counts mean different things have no sum — a day
     * count and a number are not addable, however well both sides type-checked. Read off one
     * operand's type, every position of the form answered with that one's order and the check could
     * not fire at all: positions were then read off rows, and written back, on an order that is not
     * theirs.
     */
    Carrier carrier(InputReads reads, Symbols symbols) {
        Carrier one = null;
        for (NumericTerm term : form.coefs().keySet()) {
            Carrier here = carrierOf(term, reads, symbols);
            if (here == null || (one != null && !one.equals(here))) {
                return null;
            }
            one = here;
        }
        return one;
    }

    /**
     * The order one term's own position is counted on, or null where the reading has no position
     * for it.
     *
     * <p>The position's, because that is whose values are being read and written: what a term is
     * measured at is the term's question ({@link NumericTerm#carrierAt}) and what the position holds
     * is the declaration's, and the two are answered together where the position was read.
     */
    static Carrier carrierOf(NumericTerm term, InputReads reads, Symbols symbols) {
        for (souther.compiler.inputs.Position position : reads.read().positions()) {
            if (position.term().equals(term)) {
                return term.carrierAt(position.type(), symbols);
            }
        }
        return null;
    }

    /** Whether the operator orders the values around the threshold rather than singling one out. */
    boolean orders() {
        return claim instanceof ComparisonClaim.Cut;
    }

}
