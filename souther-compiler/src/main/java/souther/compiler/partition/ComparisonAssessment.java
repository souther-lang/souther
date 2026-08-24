package souther.compiler.partition;

import souther.compiler.check.Owed;
import souther.compiler.check.Required;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.diag.Citation;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.UnreadRule;
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
 * nowhere to live. Which positions the quantity is over decides both what is owed and where the
 * border goes, because both come off {@link Cutting#dividedPosition()} and it is asked once.
 *
 * <p><b>Five ways a comparison raises nothing, and they are five.</b> Read to the end and cutting
 * nothing, naming no position at all, reading the answer, cutting where the quantity does not run,
 * and not read — each is a different sentence to whoever is told it, and only the last is about a
 * limit of this compiler. Held as one, a tautology was owed a row where the relation changes and a
 * rule this could not read was described as naming no position.
 */
sealed interface ComparisonAssessment {

    /**
     * The comparison cuts one position's own values.
     *
     * @param cutting  the line, which is what a threshold and a border are read off
     * @param position the position it divides
     * @param value    the value of the position the classes meet at, or null where the position
     *                 holds none there
     */
    record AtAPosition(Cutting cutting, NumericTerm position, Place value, Required.Places places)
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
    record AcrossPositions(Cutting cutting, Citation at, Required.Places places)
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
    record Unread(BlockReason.ReadingStopped why, List<UnreadRule.Coordinate> filedAt)
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
        // A comparison about no position of the input at all, which is neither a rule read to the
        // end nor a reading that stopped: there is nothing here for either sentence to be about.
        boolean names = !GuardThresholds.mentionedIn(comparison, reads, symbols).isEmpty();
        return switch (Cutting.read(behavior, comparison, reads, symbols, quantities)) {
            case Cutting.Read.Cuts cuts -> onTheQuantity(comparison, cuts.cutting());
            // Read to the end and cutting nothing, which is a fact about the rule and not a limit
            // of this compiler: `a <= a` holds of every row.
            case Cutting.Read.CutsNothing _ -> names ? new CutsNothing() : new NoInput();
            // And where the reading stopped, its own answer for having stopped — decided where it
            // stopped rather than worked out again from the comparison afterwards.
            case Cutting.Read.Stopped stopped -> names
                    ? new Unread(stopped.why(),
                            GuardThresholds.filedAt(comparison, reads, symbols))
                    : new NoInput();
        };
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
            return new AcrossPositions(cutting, Citation.of(comparison.pos()),
                    places(cutting, null));
        }
        Place value = cutting.singles() ? cutting.singledValue() : cutting.dividedValue();
        return new AtAPosition(cutting, divided, value, places(cutting, value));
    }

    /**
     * What the rule does to the quantity, from the canonical quantity and the operator together.
     *
     * <p>Not from the operator alone. {@code 2 * a == 8} names four and {@code 2 * a == 9} names no
     * whole number at all, under one operator: whether the value the rule wrote is one the quantity
     * holds is the quantity's answer, and it is already given by the seam the line was read off.
     */
    private static Required.Places places(Cutting cutting, Place value) {
        if (!cutting.singles()) {
            return Required.Places.ACROSS_THE_VALUE;
        }
        return value == null ? Required.Places.AT_NO_VALUE : Required.Places.AT_THE_VALUE;
    }

    /** What this raises, as the accounting names it. */
    default Required.ComparisonSubject subject() {
        return switch (this) {
            case AtAPosition at -> new Required.ComparisonSubject.AnInput(
                    subjectOf(at.position()), Owed.Subject.at(""), at.places());
            case AcrossPositions over -> new Required.ComparisonSubject.AcrossPositions(
                    new Owed.Subject.OfComparison(over.at()), over.places());
            case AnswerDependent _ -> new Required.ComparisonSubject.AnswerDependent();
            case NoInput _ -> new Required.ComparisonSubject.NoInput();
            case CutsNothing _ -> new Required.ComparisonSubject.CutsNothing();
            case OutsideTheDomain _ -> new Required.ComparisonSubject.OutsideTheDomain();
            case Unread unread -> new Required.ComparisonSubject.Unread(unread.why());
        };
    }

    /**
     * What the question is about, relative to the position it is filed at.
     *
     * <p>An invariant's subject is relative to the value its clause is on, and this is the same
     * thing one frame out. Which of the two it is was settled by the quantity that was cut: a
     * {@code String} bounded on its length raises about the string and draws its line on the count,
     * and a document promises both spellings.
     */
    private static Owed.Subject.OfAPosition subjectOf(NumericTerm term) {
        // A term that is a count says the line is on the count; anything else — a term over the
        // position's own value — leaves it on the position.
        return new Owed.Subject.OfAPosition("", term instanceof NumericTerm.SizeOf);
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
