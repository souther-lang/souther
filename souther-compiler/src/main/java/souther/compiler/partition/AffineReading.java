package souther.compiler.partition;

import souther.compiler.check.AffineForms;
import souther.compiler.check.ComparisonClaim;
import souther.compiler.check.Location;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.ReadMeaning;
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
        return read(comparison, reads, symbols) instanceof OfAComparison.Cuts cuts
                ? cuts.read() : null;
    }

    /**
     * What reading {@code comparison} as a line came to.
     *
     * <p>Three answers, because two of them used to be one absence. A reading that stopped and a
     * reading that went all the way and found no quantity are opposite facts: the first says this
     * compiler fell short, and the second says the rule cuts nothing — {@code a - a > 0} is read
     * perfectly and divides no position. Told apart only by a {@code null}, whoever asked had to
     * guess, and guessed that a rule it had read in full was written in a form it could not read.
     */
    sealed interface OfAComparison {

        /** The line the comparison draws. */
        record Cuts(AffineReading read) implements OfAComparison {

            public Cuts {
                java.util.Objects.requireNonNull(read, "a comparison that cuts has a line");
            }
        }

        /** Read to the end, and the quantity it cuts is nothing: a comparison of constants, or one
         *  whose positions cancel. Nothing is missing here. */
        record CutsNothing() implements OfAComparison {}

        /** The reading stopped, at this expression and in the environment it was being read in. */
        record Stopped(Core node, InputReads at) implements OfAComparison {

            public Stopped {
                java.util.Objects.requireNonNull(node, "a reading that stopped stopped somewhere");
                java.util.Objects.requireNonNull(at, "and was reading it in something");
            }
        }
    }

    /** The same, saying which of the three it is. */
    static OfAComparison read(Core.Binary comparison, InputReads reads, Symbols symbols) {
        if (!comparison.op().compares()) {
            return new OfAComparison.CutsNothing();
        }
        // The left first where both stop, which is the side a threshold would be read off.
        LinearForm<NumericTerm> left = null;
        for (Core side : java.util.List.of(comparison.left(), comparison.right())) {
            AffineForms.Outcome<NumericTerm, InputReads> read =
                    AffineForms.outcome(side, reads, reading(symbols));
            if (read instanceof AffineForms.Outcome.StoppedAt<NumericTerm, InputReads> stopped) {
                return new OfAComparison.Stopped(stopped.node(), stopped.at());
            }
            if (left == null) {
                left = ((AffineForms.Outcome.Composed<NumericTerm, InputReads>) read).form();
            } else {
                LinearForm<NumericTerm> whole = left.minus(
                        ((AffineForms.Outcome.Composed<NumericTerm, InputReads>) read).form());
                if (whole.coefs().isEmpty()) {
                    return new OfAComparison.CutsNothing();
                }
                AffineReading here = new AffineReading(
                        new LinearForm<>(BigDecimal.ZERO, whole.coefs()),
                        whole.constant().negate(), ComparisonClaim.of(comparison.op()));
                // Turned round here and nowhere else. `48 >= 3a + 6b` and `3a + 6b <= 48` are one
                // rule, and a reader that met the first without turning it round drew its border on
                // `-3a - 6b` — the same four points under a name no author wrote, and a different
                // line from the rule written the other way.
                return new OfAComparison.Cuts(
                        here.facesTheOtherWay(subjectOf(comparison, left, reads, symbols))
                                ? here.mirrored() : here);
            }
        }
        throw new IllegalStateException("a comparison has two sides");
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
        return AffineForms.of(e, reads, reading(symbols));
    }

    /** What this reader answers about its own environment, which is what tells its atoms from
     *  another reader's. */
    private static AffineForms.Reading<NumericTerm, InputReads> reading(Symbols symbols) {
        return new AffineForms.Reading<NumericTerm, InputReads>() {

            @Override
            public Symbols symbols() {
                return symbols;
            }

            @Override
            public LinearForm<NumericTerm> leafOf(Core node, InputReads at) {
                NumericTerm term = GuardThresholds.termOf(node, at, symbols);
                return term == null ? null : LinearForm.atom(term);
            }

            @Override
            public InputReads inside(Core.LetIn li, InputReads at) {
                return at.and(li.binder(), li.value());
            }

            /**
             * A name given arithmetic over positions, which is the arithmetic the rule cuts.
             *
             * <p>Only where the name is nothing of its own. A name that is a position is that
             * position and the leaf answers with it; a name an operation handed an element on
             * stands for one element of what the operation answered, and the expression behind it
             * was written about every element rather than about the value at this read — put where
             * the name stands, it would draw a line at a position whose values are not the ones the
             * rule is about. Which of those a name is, is one answer from one place
             * ({@link InputReads#meaningOf}), read here rather than worked out again.
             */
            @Override
            public AffineForms.ReadThrough<InputReads> readThrough(Core.Read read, InputReads at) {
                return at.meaningOf(read, symbols) instanceof ReadMeaning.Through through
                        ? new AffineForms.ReadThrough<>(through.value(), through.at()) : null;
            }

            @Override
            public boolean readsThrough(Core.FieldAccess fa, InputReads at) {
                return at.pathOf(fa.target(), symbols) == null
                        && !Location.isStep(fa.target().type(), fa.field(), symbols);
            }
        };
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
     * The order each of this form's positions is read and written back on, or null where some
     * position has no order with counts under it.
     *
     * <p>Asked of each position and not of the operand it was written beside. Read off one
     * operand's type, every position of the form answered with that one's order and the check could
     * not fire at all: positions were then read off rows, and written back, on an order that is not
     * theirs.
     *
     * <p>An order apiece rather than one for all of them, and no question here about whether the
     * form adds up to anything. Which positions may be added, and with which weights, is settled
     * before this: an arithmetic a model wrote type-checked, and one this compiler composed stands
     * on what the operation states about its result. A rule refusing forms here by comparing what
     * the orders count would be a reader deciding that again, and deciding it worse — it cannot see
     * the coefficients. {@code b + a} over two dates leaves an origin in and {@code b - a - n} does
     * not, and those two are the same orders in the same numbers.
     *
     * <p>What is asked is only that each position has an order, and that the order has counts under
     * it: a position with no number is one a sum has nothing to add.
     */
    java.util.Map<NumericTerm, souther.compiler.inputs.TermOrders> carriers(
            InputReads reads, Symbols symbols) {
        java.util.Map<NumericTerm, souther.compiler.inputs.TermOrders> on =
                new java.util.LinkedHashMap<>();
        for (NumericTerm term : form.coefs().keySet()) {
            // Both ends of the term, because a reader of a row wants the one it is decoded on and a
            // reader of a line wants the one the answer is measured on. Carried together so neither
            // stands in for the other (#1027).
            souther.compiler.inputs.TermOrders here = reads.read().ordersOf(term, symbols);
            if (here.answered() == null || !here.answered().counts()) {
                return null;
            }
            on.put(term, here);
        }
        return on.isEmpty() ? null : on;
    }

    /** Whether the operator orders the values around the threshold rather than singling one out. */
    boolean orders() {
        return claim instanceof ComparisonClaim.Cut;
    }

}
