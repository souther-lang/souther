package souther.compiler.partition;

import souther.compiler.check.AffineForms;
import souther.compiler.check.StatedComparison;
import souther.compiler.check.ComparisonClaim;
import souther.compiler.check.Location;
import souther.compiler.check.DeclarationAccess;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputNumber;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.NumericTerms;
import souther.compiler.inputs.PathResolution;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.Map;
import java.util.Objects;
import java.util.Set;

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
record AffineReading(LinearForm<NumericTerm> form, ExactRatio cut, ComparisonClaim claim) {

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

        /**
         * Read to the end, and the quantity it cuts is nothing: a comparison of constants, or one
         * whose positions cancel. Nothing is missing here.
         *
         * <p>{@code read} is every number of the input this reading named on the way, whether or not
         * it survived the cancellation. What the rule is about is not what is left of it: {@code a -
         * a <= 0} states something about {@code a} and holds of every row, and a reader told only
         * that the quantity is empty would have to go back to the operands to find out where to say
         * so — which is a second account of what the rule names, beside the reading that has just
         * read it. A comparison of constants named nothing and comes back with nothing.
         *
         * <p>A set, because naming one number twice is naming it once. Which order a document lists
         * them in is not carried here and is not the order they were met in: that is how the rule
         * was spelled, and it is settled where the coordinates are made
         * ({@link AffineReading#filedAt}).
         *
         * <p>{@code difference} is what the left side exceeds the right by, which is the same for
         * every row — so which way the comparison comes out is settled by it and the relation, and
         * a reader asking that is not sent back to the operands to fold them a second way.
         */
        record CutsNothing(java.util.Set<NumericTerm> read, ExactRatio difference)
                implements OfAComparison {

            public CutsNothing {
                read = java.util.Set.copyOf(read);
                Objects.requireNonNull(difference,
                        "a comparison that cuts nothing still has its two sides' difference");
            }

            /** Whether a comparison stating {@code rel} of its left side against its right comes
             *  out holding, which is the same for every row. */
            boolean holds(Rel rel) {
                return rel.holds(difference.signum());
            }
        }

        /**
         * Read to the end, each side as a form, and the difference of the two has no representation.
         *
         * <p>Its own answer beside {@link CutsNothing} and {@link Stopped}. Nothing cancelled, so
         * the quantity is not empty; the reading did not stop on an expression it could not read,
         * so the rule is a form it reads.
         * What is missing is a number to say what the difference is, and a reader told either of the
         * others would be told something about the rule that is not so. A rule the model wrote in
         * good faith — a coefficient at one end of the range weighed against one at the other —
         * arrives here.
         *
         * <p>{@code read} is every number of the input this reading named on the way, for the same
         * reason {@link CutsNothing} carries it.
         */
        record NotHeld(Set<NumericTerm> read) implements OfAComparison {

            public NotHeld {
                read = Set.copyOf(read);
            }
        }

        /**
         * The reading stopped: where, in what environment, and for the reason the arithmetic gave.
         * The reason is the arithmetic's own, so a reader of this takes it as it is.
         */
        record Stopped(AffineForms.Outcome.StoppedAt<NumericTerm, InputReads> failure)
                implements OfAComparison {

            public Stopped {
                java.util.Objects.requireNonNull(failure, "a reading that stopped stopped somewhere");
            }

            /** The expression the reading stopped at. */
            public Core node() {
                return failure.node();
            }

            /** The environment it was being read in. */
            public InputReads at() {
                return failure.at();
            }
        }
    }

    /** The same, of the input {@code read} reads, with the names as {@code reads} has them. */
    static OfAComparison read(StatedComparison comparison, InputReads reads, InputReading read) {
        return read(comparison, read.domain(), reads, read.rules());
    }

    /** The same, saying which of the four it is. */
    static OfAComparison read(StatedComparison comparison, InputDomain inputs, InputReads reads,
                              RuleReadingSource ruleSource) {
        // What this reading names as it goes, kept so that a reading which ran to the end can say
        // what it was about without anybody reading the comparison again.
        java.util.Set<NumericTerm> named = new java.util.LinkedHashSet<>();
        // The left first where both stop, which is the side a threshold would be read off.
        LinearForm<NumericTerm> left = null;
        for (Core side : java.util.List.of(comparison.left(), comparison.right())) {
            AffineForms.Outcome<NumericTerm, InputReads> read =
                    AffineForms.outcome(side, reads, reading(inputs, ruleSource, named));
            if (read instanceof AffineForms.Outcome.StoppedAt<NumericTerm, InputReads> stopped) {
                return new OfAComparison.Stopped(stopped);
            }
            if (left == null) {
                left = ((AffineForms.Outcome.Composed<NumericTerm, InputReads>) read).form();
            } else {
                // Each side was read as a form, and the difference of the two is what the rule is
                // about. Two forms held one by one can have a difference no ratio holds — a
                // coefficient at one end of the exponents against one at the other — and that is a
                // reading that ran to the end and could not write down what it found, which is
                // neither a rule with no line nor a form the arithmetic did not read.
                if (!(left.minus(
                        ((AffineForms.Outcome.Composed<NumericTerm, InputReads>) read).form())
                        instanceof ExactAnswer.Held<LinearForm<NumericTerm>> difference)) {
                    return new OfAComparison.NotHeld(named);
                }
                LinearForm<NumericTerm> whole = difference.value();
                if (whole.coefs().isEmpty()) {
                    return new OfAComparison.CutsNothing(named, whole.constant());
                }
                AffineReading here = new AffineReading(
                        new LinearForm<>(ExactRatio.ZERO, whole.coefs()),
                        whole.constant().negated(), comparison.claim());
                // Turned round here and nowhere else. `48 >= 3a + 6b` and `3a + 6b <= 48` are one
                // rule, and a reader that met the first without turning it round drew its border on
                // `-3a - 6b` — the same four points under a name no author wrote, and a different
                // line from the rule written the other way.
                return new OfAComparison.Cuts(
                        here.facesTheOtherWay(subjectOf(comparison.left(), left, reads, ruleSource))
                                ? here.mirrored() : here);
            }
        }
        throw new IllegalStateException("a comparison has two sides");
    }

    /**
     * The line {@code form stated 0} draws, where {@code form} is over the input's numbers alone.
     *
     * <p>What a comparison states is read once ({@link Pullback#ofAComparison}), and this is that
     * statement put on the input space: the constant moved to the threshold, and the form faced the
     * way the comparison's left side names ({@link #facesTheOtherWay}). The facing is how the line is
     * named in a report and not what it is: the two ways are one statement.
     *
     * @param leftSide the comparison's left side as written, which is only asked which position it
     *                 names first
     */
    static AffineReading stating(LinearForm<NumericTerm> form, Rel stated, Core leftSide,
                                 InputReads reads, RuleReadingSource ruleSource) {
        AffineReading here = new AffineReading(new LinearForm<>(ExactRatio.ZERO, form.coefs()),
                form.constant().negated(), ComparisonClaim.stating(stated));
        return here.facesTheOtherWay(subjectOf(leftSide, form, reads, ruleSource))
                ? here.mirrored() : here;
    }

    /**
     * The order a form's positions are named in, which settles what "the first coefficient" means.
     *
     * <p>By the position's own name, because that is the one thing about a form that does not depend
     * on how it was written. A form is a map; the order its coefficients were recorded in is the
     * order the author happened to add them in, and a report is a document compared against the one
     * written last time.
     */
    static java.util.List<Map.Entry<NumericTerm, ExactRatio>> ordered(
            LinearForm<NumericTerm> form) {
        return NumericTerms.entriesInOrder(form.coefs());
    }

    /**
     * Where a reading that reached the numbers files what it found, in the order a document names
     * them.
     *
     * <p><b>The numbers and not the places they sit at.</b> A reader that got as far as the terms
     * has the operation each number is taken by, and two operations over one path are two rules a
     * report has to tell apart ({@link souther.compiler.inputs.FilingCoordinate}); the coordinate
     * that names only the place is for a reader that did not get that far. Written out again at a
     * second reader, the weaker of the two is the one that would be reached for, since a path is
     * what every term can be asked for.
     *
     * <p>By the term's own name, for the reason {@link #ordered} gives: how a rule was spelled is
     * not what a document is keyed on, and a report is compared against the one written last time.
     * So the order the reading happened to meet them in is not carried, and neither is a set's.
     */
    static java.util.List<souther.compiler.inputs.FilingCoordinate> filedAt(
            java.util.Collection<NumericTerm> terms) {
        return souther.compiler.inputs.NumericTerms.inOrder(terms).stream()
                .<souther.compiler.inputs.FilingCoordinate>map(
                        souther.compiler.inputs.FilingCoordinate::of)
                .distinct().toList();
    }

    /**
     * What this reader answers about its own environment, which is what tells its atoms from
     * another reader's.
     *
     * <p>{@code named} takes every number this names, which is the one place a node of the tree
     * becomes a term of the input. Collected here rather than recovered afterwards: what a rule is
     * about is what the reading of it named, and a reader working that out again from the operands
     * is a second account of it.
     *
     * <p>{@code inputs} is held here and not threaded through the walk. What the environment
     * answers changes at every binding the walk goes under; the reading of the input is one value
     * for the whole reading of one comparison, and this reader lives exactly that long.
     */
    private static AffineForms.Reading<NumericTerm, InputReads> reading(
            InputDomain inputs, RuleReadingSource ruleSource, java.util.Set<NumericTerm> named) {
        return new AffineForms.Reading<NumericTerm, InputReads>() {

            @Override
            public Symbols symbols() {
                return ruleSource.symbols();
            }

            @Override
            public DeclarationAccess declarations() {
                return ruleSource.declarations();
            }

            @Override
            public LinearForm<NumericTerm> leafOf(Core node, InputReads at) {
                NumericTerm term = InputNumber.of(node, inputs, at, ruleSource);
                if (term == null) {
                    return null;
                }
                named.add(term);
                return LinearForm.atom(term);
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
                return NameAnswers.denoting(read, at, ruleSource.symbols(),
                        ruleSource.newtypes());
            }

            /**
             * A name an operation handed an element on, where the container was written out. Read
             * for the count the one answer comes back with, beside the walk that says which
             * positions a rule is about, so the two meet a plurality with the same knowledge.
             */
            @Override
            public java.util.List<AffineForms.ReadThrough<InputReads>> alternativesOf(
                    Core.Read read, InputReads at) {
                return NameAnswers.alternativesOf(read, at, ruleSource.symbols(),
                        ruleSource.newtypes());
            }

            @Override
            public AffineForms.ReadThrough<InputReads> taken(Core node, InputReads at) {
                return NameAnswers.taken(node, at);
            }

            @Override
            public LinearForm<Core> takenAsAForm(Core node, InputReads at) {
                return NameAnswers.takenAsAForm(node, at);
            }

            @Override
            public boolean readsThrough(Core.FieldAccess fa, InputReads at) {
                // Read through where the target is at no position of the input: a field of a value
                // that stands nowhere is arithmetic's to walk into, since it is no place a row
                // writes at.
                boolean stands = switch (at.pathOf(fa.target(), ruleSource.newtypes())) {
                    case PathResolution.At _ -> true;
                    case PathResolution.NotAPosition _ -> false;
                    // A target that may stand at a position of the input does, on some run, and
                    // which is not for arithmetic to decide by walking into it. Read through, a
                    // field of it would be a term over a place it may never stand at.
                    case PathResolution.MayStandAt _ -> true;
                };
                return !stands
                        && !Location.isStep(fa.target().type(), fa.field(), ruleSource.newtypes());
            }
        };
    }

    /** The one position this cuts where it cuts one with a coefficient of one, or null. A form
     *  written {@code -x} has already been turned round by the reading that made it
     *  ({@link #read}), so this asks about the coefficient as the canonical form has it. */
    NumericTerm oneCoordinate() {
        if (form.coefs().size() != 1) {
            return null;
        }
        Map.Entry<NumericTerm, ExactRatio> only = form.coefs().entrySet().iterator().next();
        return only.getValue().equals(ExactRatio.ONE) ? only.getKey() : null;
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
        for (Map.Entry<NumericTerm, ExactRatio> each : form.coefs().entrySet()) {
            if (each.getValue().equals(ExactRatio.ONE)) {
                on = each.getKey();
            } else if (each.getValue().equals(ExactRatio.ONE.negated())) {
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
        return new AffineReading(form.negate(), cut.negated(), claim.turned());
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
        ExactRatio first = subject == null ? null : form.coefs().get(subject);
        return (first != null ? first : ordered(form).getFirst().getValue()).signum() < 0;
    }

    /** The position the comparison's left side names first among the terms of {@code left}, or null
     *  where it names none of them. Handed what was read rather than walking it again: one
     *  comparison is read once. */
    private static NumericTerm subjectOf(Core leftSide, LinearForm<NumericTerm> left,
                                         InputReads reads, RuleReadingSource ruleSource) {
        if (left == null || left.coefs().isEmpty()) {
            return null;
        }
        for (souther.compiler.inputs.TermPath named
                : GuardThresholds.mentionedIn(leftSide, reads, ruleSource.symbols(),
                        ruleSource.newtypes(),
                        // A side of a comparison and not a clause: what this is handed is the side
                        // alone, and rooting a reading of arrivals at it would read it as a tree of
                        // its own and lose whatever bound a name above it.
                        souther.compiler.coverage.Arrivals.everyArmIsTakenForAValue())) {
            for (NumericTerm atom : NumericTerms.inOrder(left.coefs().keySet())) {
                if (atom.subjectPath().equals(named)) {
                    return atom;
                }
            }
        }
        return null;
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
            souther.compiler.inputs.Quantities quantities) {
        java.util.Map<NumericTerm, souther.compiler.inputs.TermOrders> on =
                new java.util.LinkedHashMap<>();
        for (NumericTerm term : NumericTerms.inOrder(form.coefs().keySet())) {
            // Both ends of the term, because a reader of a row wants the one it is decoded on and a
            // reader of a line wants the one the answer is measured on. Carried together so neither
            // stands in for the other (#1027).
            souther.compiler.inputs.TermOrders here = quantities.ordersOf(term);
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
