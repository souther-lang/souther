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
import java.util.Optional;

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
 * <p><b>Six ways a comparison leaves the positions nothing, and they are six.</b> Read to the end
 * and cutting nothing, naming no position at all, reading the answer, cutting where the quantity
 * does not run, cutting where the rows that arrive stop short, and not read — each is a different
 * sentence to whoever is told it, and only the last is about a limit of this compiler. Held as one,
 * a tautology was owed a row where the relation changes and a rule this could not read was
 * described as naming no position.
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
    record AtAPosition(Cutting cutting, NumericTerm.FromOnePosition position, Place value,
                       Places places)
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

        /** Whether what it cuts is a number read over a run of values rather than a form over
         *  positions, which is a different thing to tell a reader who found no partition. */
        boolean overARun() {
            return cutting.quantity().direction().keySet().stream()
                    .anyMatch(term -> term.atOnePosition() == null);
        }
    }

    /** The comparison reads what the behavior answers. */
    record AnswerDependent() implements ComparisonAssessment {}

    /** The comparison names no position of the behavior's input. */
    record NoInput() implements ComparisonAssessment {}

    /**
     * Read to the end, and the quantity it cuts is nothing: the positions cancel.
     *
     * <p>{@code filedAt} is where the rule is said to have cut nothing, and it comes off the
     * reading rather than off a second walk over the operands. What is left of the quantity is not
     * what the rule is about — {@code a - a <= 0} is about {@code a} and cuts nothing — so the
     * coordinates are the numbers the reading named, whether or not they survived, and they are the
     * numbers rather than the places they sit at ({@link AffineReading#filedAt}).
     */
    record CutsNothing(List<FilingCoordinate> filedAt) implements ComparisonAssessment {

        public CutsNothing {
            filedAt = List.copyOf(filedAt);
        }
    }

    /** Read in full, and the quantity does not run as far as the line the rule draws. */
    record OutsideTheDomain(Cutting cutting) implements ComparisonAssessment {

        public OutsideTheDomain {
            if (cutting == null) {
                throw new IllegalArgumentException("a line outside the domain is still a line");
            }
        }
    }

    /**
     * Read in full, the quantity runs as far as the line — and no row that arrives at the
     * comparison holds a value at it.
     *
     * <p>Its own answer and not {@link OutsideTheDomain}, which is a fact about the declarations
     * alone and holds wherever the comparison stands. This one is about the place: the guards above
     * the comparison rule the line's values out, so the classes it would make are classes of
     * nothing and the rows they would ask for are rows nothing can write. An author told the first
     * would look at the rule for a line their declarations refuse, and the line is fine — what
     * refuses it is on the way.
     *
     * <p>Only a proof lands here: the whole state at the comparison shown empty, or the values that
     * arrive shown to stop short of the line. A comparison nothing could project an arrival for
     * keeps its line ({@link souther.compiler.reach.ComparisonArrival.NoProjection}).
     */
    record NothingArrivesAtItsLine(Cutting cutting) implements ComparisonAssessment {

        public NothingArrivesAtItsLine {
            if (cutting == null) {
                throw new IllegalArgumentException(
                        "a line nothing arrives at is still a line somebody wrote");
            }
        }
    }

    /**
     * Read in full, and the rules leave no input for any line to be about.
     *
     * <p>Its own answer and not {@link OutsideTheDomain}, which says the quantity exists and does
     * not run as far as this rule's line. Here nothing runs anywhere: the declarations reaching this
     * input admit no value at all, so neither this line nor any other is outside anything. Said as
     * the first, an author is sent to look at one rule for a contradiction that is not in it — two
     * clauses each admitting values are empty together, and neither of them is the one that failed.
     *
     * <p>Whose emptiness it is is the input's and not this comparison's. A quantity is a function of
     * the input, so a quantity's values are empty exactly when the input's are — asked of the
     * quantity, this would be a second reader deciding what the rules admit, and the two would
     * disagree about a model wherever one of them read a rule the other did not.
     */
    record NoFeasibleInput(souther.compiler.inputs.EmptyInput why, Cutting cutting)
            implements ComparisonAssessment {

        public NoFeasibleInput {
            if (why == null || cutting == null) {
                throw new IllegalArgumentException(
                        "an input the rules leave empty is still a line somebody wrote");
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
    record Unread(BlockReason.RuleReadingStopped why, List<FilingCoordinate> filedAt)
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
     *
     * <p><b>The arithmetic answers before anything else is asked.</b> Which positions a rule is
     * about is what the quantity it cuts is over: every atom of a form is a number of a location
     * ({@link souther.compiler.inputs.InputNumber}), so a comparison that came to a line is about
     * the positions of that line and there is nothing left to look up. What the walk over the
     * expression says a side is made of is the answer for a rule that came to no line — where it is
     * the only account there is — and asked first it would be a second reading standing in front of
     * the first, able to veto it and never to add to it: two members of a written list holding one
     * form written two ways agree as arithmetic and are made of different things, so the rule they
     * state would come back as one about no input at all.
     */
    static ComparisonAssessment of(String behavior, Core.Binary comparison,
                                   souther.compiler.inputs.InputDomain inputs, InputReads reads,
                                   Symbols symbols, Quantities quantities, BindingId answer,
                                   boolean drawnByAnInvariant,
                                   souther.compiler.reach.ComparisonArrival arrival) {
        // Asked first, and of the whole comparison. A rule that reads the answer anywhere in it is
        // one this reading does not put on the input space, whichever side the answer is on and
        // whatever else stands beside it: `value.n + query.offset <= 20` is about the answer and
        // about an input, and the input is no more measurable here for the input being named.
        if (readsAnswer(comparison, answer)) {
            return new AnswerDependent();
        }
        return switch (Cutting.read(behavior, comparison, inputs, reads, symbols, quantities)) {
            case Cutting.Read.Cuts cuts ->
                    onTheQuantity(comparison, cuts.cutting(), quantities, drawnByAnInvariant,
                            arrival);
            // Read to the end and cutting nothing, which is a fact about the rule and not a limit
            // of this compiler: `a <= a` holds of every row. Where the comparison names no position
            // either, there is no rule about a position to say it of — `2 > 1` is a comparison of
            // constants and states nothing anywhere.
            case Cutting.Read.CutsNothing over -> over.read().isEmpty()
                    ? aboutNoPosition(comparison, reads, symbols)
                    : new CutsNothing(AffineReading.filedAt(over.read()));
            // And where the reading stopped, its own answer for having stopped — decided where it
            // stopped rather than worked out again from the comparison afterwards. Here the walk
            // over the expression is the only account of what the rule is about, which is what it
            // is for.
            case Cutting.Read.Stopped stopped -> {
                List<FilingCoordinate> filedAt =
                        GuardThresholds.filedAt(comparison, inputs, reads, symbols);
                yield filedAt.isEmpty() ? aboutNoPosition(comparison, reads, symbols)
                        : new Unread(stopped.why(), filedAt);
            }
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
    private static ComparisonAssessment onTheQuantity(
            Core.Binary comparison, Cutting cutting, Quantities quantities,
            boolean drawnByAnInvariant, souther.compiler.reach.ComparisonArrival arrival) {
        // Whether there is an input at all, before anything is asked about where its values run.
        // A quantity is a function of the input, so where the rules admit no input they admit no
        // value of any quantity — and every question below is about one quantity's values against
        // one rule's line, which is a question about a model that has some.
        java.util.Optional<souther.compiler.inputs.EmptyInput> empty = quantities.emptiness();
        if (empty.isPresent()) {
            return new NoFeasibleInput(empty.get(), cutting);
        }
        // The line and not one of its points. A rule drawing where the quantity never reaches
        // divides the position into nothing, and a reader told that the rule went unread would go
        // looking for a limit of this compiler that is not there.
        if (!Border.reaches(cutting.at(), cutting.seam(),
                Border.satisfyingSide(cutting.holdsAtTheValue(), cutting.valueBelongsBelow()),
                Border.ordersAroundTheCut(drawnByAnInvariant, cutting.singles()),
                cutting.within())) {
            return new OutsideTheDomain(cutting);
        }
        // The declarations first and the place second, because the two are different sentences and
        // the first holds wherever the comparison stands. The place answers as two nested domains
        // around one line: what the declarations leave, and that met with what arrives — the same
        // predicate on the narrower domain, not a second reading of the rule. Only a proof drops a
        // line; an arrival nothing could project restricts nothing and the line stands.
        switch (arrival) {
            case souther.compiler.reach.ComparisonArrival.NothingArrives _ -> {
                return new NothingArrivesAtItsLine(cutting);
            }
            case souther.compiler.reach.ComparisonArrival.Values values -> {
                if (!Border.reaches(cutting.at(), cutting.seam(),
                        Border.satisfyingSide(cutting.holdsAtTheValue(),
                                cutting.valueBelongsBelow()),
                        Border.ordersAroundTheCut(drawnByAnInvariant, cutting.singles()),
                        cutting.withinGiven(values))) {
                    return new NothingArrivesAtItsLine(cutting);
                }
            }
            case souther.compiler.reach.ComparisonArrival.NoProjection _ -> { }
        }
        NumericTerm.FromOnePosition divided = cutting.dividedPosition();
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
            case NothingArrivesAtItsLine unarrived -> unarrived.cutting().over();
            // The positions its quantity is over, as every read rule's are. That the rules leave
            // the input empty says nothing about which positions this rule is about.
            case NoFeasibleInput none -> none.cutting().over();
            case Unread unread -> unread.filedAt();
            case CutsNothing cuts -> cuts.filedAt();
            case AtAPosition _, AnswerDependent _, NoInput _ -> List.of();
        };
    }

    /**
     * Why the reading of lines drew none from this comparison, or empty where it drew one.
     *
     * <p><b>Named for the reading it is the answer of, and not for the assessment it is read
     * off.</b> What a comparison comes to is one decision; what a reading makes of it is that
     * reading's own, and the two do not agree even about one comparison — a rule relating two
     * positions is read here from end to end and places no line, and the reading that turns clauses
     * into sets of values gets nothing it can hold from the same rule. A name saying only that a
     * reason was read off an assessment would be reached for by that reader too, and the answer it
     * would take is the one that says nothing fell short.
     *
     * <p>Answered once, here. Both producers of this evidence — a clause of an {@code ensures} and a
     * {@code guard}'s comparison — worked the same table out separately, so a case added to
     * {@link ComparisonAssessment} had to be answered twice and the two could disagree about one
     * comparison. That is the shape this whole type was made to have none of.
     *
     * <p>Empty rather than null, and no {@code default} on the switch. A comparison that drew a
     * line, one about no position of the input, and one about what the behavior answers each leave
     * nothing for a reader to be told, and saying so with an absent value made the absence a
     * sentinel one caller had to remember to test for. An arm added is a compile error in this
     * method and in the value reading's own beside it, which is the point of neither having a
     * default.
     */
    default Optional<BlockReason.RuleWithoutLineReason> whyTheLineReadingDrewNone() {
        return switch (this) {
            // Which of the two a form that divides nothing is: a line over a run is one number and
            // one line with no position under it, and a line over several positions is a relation
            // between them. Answered from what the quantity is over rather than by the count of its
            // terms, since a form of one term is either.
            case AcrossPositions across -> Optional.of(across.overARun()
                    ? new BlockReason.ComparisonOverARun()
                    : new BlockReason.ComparisonBetweenPositions());
            case CutsNothing _ -> Optional.of(new BlockReason.ComparisonCuttingNothing());
            case OutsideTheDomain _ ->
                    Optional.of(new BlockReason.ComparisonCuttingOutsideDomain());
            // Not the reason above: there the declarations never run as far as the line, and here
            // they do — what stops short of it is the values that arrive at the comparison, ruled
            // out by the guards on the way. An author reading the first would look at one rule for
            // a contradiction with their declarations that is not in it.
            case NothingArrivesAtItsLine _ ->
                    Optional.of(new BlockReason.ComparisonNothingArrivesAtItsLine());
            // Nothing about this rule fell short, and nothing about this rule is what happened. The
            // rules of the input admit no value between them, which is one fact about the behavior
            // and not one per rule at each position it names — said here, a model with two clauses
            // and four positions would be told eight times, and each time about a rule that is not
            // the one at fault.
            case NoFeasibleInput _ -> Optional.empty();
            // Its own answer for having stopped, decided where it stopped. Worked out again from
            // the comparison afterwards, one whose carrier stopped the reading came back as a rule
            // that relates two positions — a sentence saying no measure is short of anything, over
            // a model missing a border.
            case Unread unread -> Optional.of(unread.why());
            case AtAPosition _, NoInput _, AnswerDependent _ -> Optional.empty();
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
            case AnswerDependent _, NoInput _, CutsNothing _, OutsideTheDomain _,
                 NothingArrivesAtItsLine _, NoFeasibleInput _, Unread _ -> false;
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
