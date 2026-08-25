package souther.compiler.partition;

import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.diag.Citation;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.FilingCoordinate;
import souther.compiler.numeric.Place;
import souther.compiler.types.BindingId;

import java.util.List;

/**
 * What one comparison comes to on the input space: one reading, and everything read off it.
 *
 * <p><b>One decision with several projections, and not several decisions about one comparison.</b>
 * What a comparison cuts is {@link Cutting}'s one answer, taken from the canonical form the
 * arithmetic reads. What the comparison is a rule <em>about</em> used to be worked out beside that,
 * from the operands as they were written — and the two disagreed. {@code a + 1 <= 10} cut position
 * {@code a} at nine and was classified as naming no position, so a border was drawn and no
 * obligation recorded against it; {@code a <= b - b + 9} cut the same position at the same value and
 * was classified as a rule about a pair, so the question raised was about a place that rule never
 * stopped. A rule was measured by one reading and reported by the other.
 *
 * <p>So the subject is derived here, from the same value the line is, and the disagreement has
 * nowhere to live. Which positions the quantity is over decides both what the rule is about and
 * where the border goes, because both come off {@link Cutting#dividedPosition()} and it is asked
 * once.
 *
 * <p><b>And what a read comparison owes is owed by having been read.</b> The rows at the value it
 * singles out, and the rows in the classes its line makes, are asked for by the reading that found
 * the line — there is no moment at which such a demand is outstanding. So they are the partition's
 * geometry and not a coverage question standing against an answer: carried as both, one decision
 * had two representations again, and the second had no reader once it could never go unanswered.
 *
 * <p><b>Five ways a comparison leaves the positions nothing, and they are five.</b> Read to the end
 * and cutting nothing, naming no position at all, reading the answer, cutting where the quantity
 * does not run, and not read — each is a different sentence to whoever is told it, and only the last
 * is about a limit of this compiler. Held as one, a tautology was owed a row where the relation
 * changes and a rule this could not read was described as naming no position.
 */
sealed interface ComparisonAssessment {

    /**
     * What a comparison does to the quantity it cuts.
     *
     * <p>Read off the canonical quantity together with the operator, and read once. The operator
     * alone does not answer it: {@code 2 * a == 8} names four and {@code 2 * a == 9} names no whole
     * number at all, under one operator and one shape of rule.
     */
    enum Places {

        /** An order across the line, so rows are owed either side of it and the two sides have
         *  roles. */
        ACROSS_THE_VALUE,

        /** One value put in a class of its own, which has no sides: the values either side of it
         *  are one class. */
        AT_THE_VALUE,

        /** A value the quantity does not hold, which puts nothing in a class of its own. */
        AT_NO_VALUE
    }

    /**
     * The comparison cuts one position's own values.
     *
     * @param cutting  the line, which is what a threshold and a border are read off
     * @param position the position it divides
     * @param value    the value of the position the classes meet at, or null where the position
     *                 holds none there
     */
    record AtAPosition(Cutting cutting, NumericTerm position, Place value, Places places)
            implements ComparisonAssessment {

        public AtAPosition {
            if (cutting == null || position == null || places == null) {
                throw new IllegalArgumentException("a line on a position names the position");
            }
        }
    }

    /**
     * The comparison cuts a form over more than one position, so it divides none of them.
     *
     * <p>A distance and a general form alike. What coverage asks of both is one question — no
     * position is divided, and the place is the comparison's to name — and which of the two shapes
     * the quantity is stays with the quantity.
     */
    record AcrossPositions(Cutting cutting, Citation at, Places places)
            implements ComparisonAssessment {

        public AcrossPositions {
            if (cutting == null || at == null || places == null) {
                throw new IllegalArgumentException("a line over a form names the form");
            }
        }
    }

    /** The comparison reads what the behavior answers. */
    record AnswerDependent() implements ComparisonAssessment {}

    /** The comparison names no position of the behavior's input. */
    record NoInput() implements ComparisonAssessment {}

    /** Read to the end, and the quantity it cuts is nothing: the positions cancel. */
    record CutsNothing() implements ComparisonAssessment {}

    /** Read in full, and the quantity does not run as far as the line the rule draws. */
    record OutsideTheDomain(Cutting cutting) implements ComparisonAssessment {

        public OutsideTheDomain {
            if (cutting == null) {
                throw new IllegalArgumentException("a line outside the domain is still a line");
            }
        }
    }

    /**
     * The comparison names a position and the reading of it stopped.
     *
     * <p>Only a reason that says a reading stopped, which the type is what enforces. A rule read to
     * the end that divides no one position has its own arms here, and their reasons say nothing
     * fell short — handed to this one, a comparison whose carrier could not be read was described
     * as relating two positions, and a model short of a border came back complete.
     *
     * @param filedAt where the reading was looking, which is a diagnostic position and never the
     *                subject of a question. What such a rule is about is the part that was not read
     */
    record Unread(BlockReason.ReadingStopped why, List<FilingCoordinate> filedAt)
            implements ComparisonAssessment {

        public Unread {
            if (why == null) {
                throw new IllegalArgumentException("a reading that stopped says why");
            }
            filedAt = List.copyOf(filedAt);
        }
    }

    /**
     * What {@code comparison} comes to, whoever wrote it.
     *
     * <p>The one way in. {@code answer} is the binding a clause calls what the behavior answers, or
     * null where the comparison is written in a body and there is nothing to be the answer.
     */
    static ComparisonAssessment of(String behavior, Core.Binary comparison, InputReads reads,
                                   Symbols symbols, Quantities quantities, BindingId answer) {
        // Asked first, and of the whole comparison. A rule that reads the answer anywhere in it is
        // one this reading does not put on the input space, whichever side the answer is on and
        // whatever else stands beside it: `value.n + query.offset <= 20` is about the answer and
        // about an input, and the input is no more measurable here for the input being named.
        if (readsAnswer(comparison, answer)) {
            return new AnswerDependent();
        }
        List<FilingCoordinate> filedAt = GuardThresholds.filedAt(comparison, reads, symbols);
        if (filedAt.isEmpty()) {
            return aboutNoPosition(comparison, reads, symbols);
        }
        return switch (Cutting.read(behavior, comparison, reads, symbols, quantities)) {
            case Cutting.Read.Cuts cuts -> onTheQuantity(comparison, cuts.cutting());
            // Read to the end and cutting nothing, which is a fact about the rule and not a limit
            // of this compiler: `a <= a` holds of every row.
            case Cutting.Read.CutsNothing _ -> new CutsNothing();
            // And where the reading stopped, its own answer for having stopped — decided where it
            // stopped rather than worked out again from the comparison afterwards.
            case Cutting.Read.Stopped stopped -> new Unread(stopped.why(), filedAt);
        };
    }

    /**
     * What a comparison naming no position of the input comes to.
     *
     * <p>Two answers and not one. A comparison of constants is about nowhere, and there is nothing
     * for a sentence about a position to be about. A comparison over values an operation answered
     * is about somewhere — the position those values came from — and what the rule says about the
     * values <em>there</em> is what would take inverting whatever the operation did. Held alike,
     * the second went out as a rule about nothing, and the position it plainly concerns came back
     * as one the model states nothing about.
     */
    private static ComparisonAssessment aboutNoPosition(Core.Binary comparison, InputReads reads,
                                                        Symbols symbols) {
        List<souther.compiler.inputs.TermPath> from = new java.util.ArrayList<>();
        GuardThresholds.cameFrom(comparison, reads, symbols, from);
        if (from.isEmpty()) {
            return new NoInput();
        }
        return new Unread(new BlockReason.RuleAboutADerivedValue(),
                from.stream().map(FilingCoordinate::at).toList());
    }

    /** What a line comes to on the input space, from the quantity it is on. */
    private static ComparisonAssessment onTheQuantity(Core.Binary comparison, Cutting cutting) {
        // The line and not one of its points. A rule drawing where the quantity never reaches
        // divides the position into nothing, and a reader told that the rule went unread would go
        // looking for a limit of this compiler that is not there.
        if (!Border.reaches(cutting.target(), cutting.within())) {
            return new OutsideTheDomain(cutting);
        }
        NumericTerm divided = cutting.dividedPosition();
        if (divided == null) {
            // Named by the comparison that drew it, which is the one thing about such a place this
            // compiler can always say exactly. It is on no position, and writing it out would be as
            // much of it as a pretty-printer got.
            return new AcrossPositions(cutting, Citation.of(comparison.pos()), places(cutting));
        }
        Place value = cutting.singles() ? cutting.singledValue() : cutting.dividedValue();
        return new AtAPosition(cutting, divided, value, places(cutting));
    }

    /**
     * What the rule does to the quantity, from the canonical quantity and the operator together.
     *
     * <p>Not from the operator alone. {@code 2 * a == 8} names four and {@code 2 * a == 9} names no
     * whole number at all, under one operator: whether the value the rule wrote is one the quantity
     * holds is the quantity's answer, and it is asked of the quantity.
     *
     * <p>Asked of whether a value of a <em>position</em> could be written instead, a form over
     * several positions has none at all — so {@code a + b == 10}, which takes ten, came back naming
     * no value the quantity holds, alongside {@code 2 * a + 2 * b == 9}, which does not.
     */
    private static Places places(Cutting cutting) {
        if (!cutting.singles()) {
            return Places.ACROSS_THE_VALUE;
        }
        return cutting.takesTheValueItNames() ? Places.AT_THE_VALUE : Places.AT_NO_VALUE;
    }

    /**
     * Where a reader is sent for what this leaves the positions with, or empty where it leaves them
     * nothing.
     *
     * <p><b>Whose answer it is turns on whether the quantity was reached.</b> A rule that was read
     * is about its quantity, so the positions it is filed at are the quantity's — {@code a + b - b
     * + c <= 10} is {@code a + c <= 10}, and a note at {@code b} would say the rule relates a
     * position it does not mention. A reading that stopped has no quantity to be about, so the
     * positions the walk met are the whole of what can be said, and nothing here may be read as
     * what the rule is about.
     *
     * <p>A quantity that came out empty is the third: there are no coordinates to file at, and the
     * positions the comparison names are what makes {@code a <= a} worth saying at all — the model
     * names a position there and cuts nothing.
     *
     * <p>Answered here so that no caller chooses. Chosen at the two producers, one of them reached
     * for the walk's positions because that was the helper in hand, and a rule read from end to end
     * was filed at a position its arithmetic had cancelled.
     */
    default List<FilingCoordinate> filedAt(Core.Binary comparison, InputReads reads,
                                                Symbols symbols) {
        return switch (this) {
            case AcrossPositions over -> over.cutting().over();
            case OutsideTheDomain outside -> outside.cutting().over();
            case Unread unread -> unread.filedAt();
            case CutsNothing _ -> GuardThresholds.filedAt(comparison, reads, symbols);
            case AtAPosition _, AnswerDependent _, NoInput _ -> List.of();
        };
    }

    /**
     * Whether this line is one a border is built on.
     *
     * <p>Only where the rule orders the values around it. A value singled out has no sides — the
     * values either side of it are one class — so there is nothing for a border to owe a row away
     * from, and a rule that names a value the quantity does not hold names no place at all.
     */
    default boolean drawsABorder() {
        return switch (this) {
            case AtAPosition at -> at.places() == Places.ACROSS_THE_VALUE;
            case AcrossPositions over -> over.places() == Places.ACROSS_THE_VALUE;
            case AnswerDependent _, NoInput _, CutsNothing _, OutsideTheDomain _, Unread _ -> false;
        };
    }

    /**
     * Whether anything in {@code e} reads the binding a rule calls the answer.
     *
     * <p>A mechanical predicate over the tree, and it classifies nothing by itself. Two readers ask
     * it and reach different conclusions: {@link #of} answers that the comparison raises no
     * input-coverage obligation, and {@link EnsuresThresholds} answers that a rule about the answer
     * is not one this compiler failed to read. Written twice, the two came apart — the second had
     * the predicate and the first did not — so it is written once and neither reader owns what the
     * other makes of it.
     *
     * <p>Syntactic. {@code value.n - value.n + query.limit.value <= 20} does not depend on the
     * answer once the arithmetic is read, and this answers that it does. The atoms of the canonical
     * form are the input's positions, so the arithmetic cannot see through a read of the answer at
     * all; a predicate that quietly did some of the cancelling would be a second reading of the
     * comparison, which is the shape this whole assessment is written against.
     *
     * <p>False where there is no answer to read, which is every comparison written in a body.
     */
    static boolean readsAnswer(Core e, BindingId answer) {
        if (answer == null) {
            return false;
        }
        if (e instanceof Core.Read read && answer.equals(read.binding())) {
            return true;
        }
        boolean[] found = {false};
        Core.forEachChild(e, child -> found[0] |= readsAnswer(child, answer));
        return found[0];
    }
}
