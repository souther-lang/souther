package souther.compiler.partition;

import souther.compiler.carrier.Lookup;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.PathResolution;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.ConditionJoin;
import souther.compiler.types.ModelOccurrence;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

/**
 * What a row has already had to satisfy by the time it arrives at one comparison.
 *
 * <p>The region a border a guard owes is searched in. A guard states a threshold and narrows no
 * declaration, so what the positions are declared to hold is the same everywhere in a body while
 * what actually arrives at a comparison deep in one is not — and a row for a border down there,
 * looked for over the declared domains, is looked for outside the region as readily as inside it.
 *
 * <p><b>Collected where the condition is assumed, and never worked out afterwards from where a
 * comparison sits.</b> A reading that walked back up the tree would be a second account of what was
 * assumed, free to name a condition nothing here could take in — and a region narrowed on a
 * condition nothing established is narrower than the rows that arrive, which is the one direction
 * that takes a coverage item away. So what is here is what the walk itself put in.
 *
 * <p><b>Including what it could not put in.</b> A condition the arithmetic has no word for narrows
 * nothing, and it is written down all the same: what a region is is one question and how it came to
 * be that region is another, and only the second can tell a search that ran over what the
 * declarations leave because nothing stood in the way from one that ran over the same box because a
 * guard above could not be read. Held as {@link OnTheWay}, so the two are one sequence in the order
 * the walk met them rather than a list and a silence.
 *
 * <p><b>Its own value and not its arm.</b> Under {@code A && B} the {@code then} arm is reached with
 * both holding, and the {@code else} arm with neither settled — a row can be in it for failing
 * either. Under {@code A || B} it is the other way round. Which of the two a comparison is in is
 * {@link GuardThresholds}'s reading of the condition, and taking an arm for a conjunct is how a
 * region would come to exclude rows that reach the guard.
 *
 * <p>Nothing here says a row that satisfies all of this arrives. A condition of a shape the
 * arithmetic cannot read is on the list without narrowing anything, so a region built from this
 * holds every row that arrives and may hold rows that do not — which is what {@link SearchRegion}
 * promises and what a proof of unreachability rests on. It is the inclusion and not a strict one:
 * a condition nothing took in may be implied by the ones that were, or hold of every row. Being on
 * the list is what lets a report say a condition is unaccounted for; it is not what the region is
 * built from.
 */
public record ReachingCuts(Lookup<ModelOccurrence, List<OnTheWay>> byComparison) {

    public static final ReachingCuts NONE = new ReachingCuts(Lookup.built(_ -> { }));

    public ReachingCuts {
        Objects.requireNonNull(byComparison, "what a walk collected, comparison by comparison");
    }

    /**
     * How a row for a border on the rule stated at {@code states} came to be looked for where it is:
     * the whole account of the walk to it.
     *
     * <p>Empty where nothing was collected there — and the answer says so, rather than leaving a
     * reader to tell a comparison at the top of a body from one this could read nothing on the way
     * to. Both leave a region as wide as the declarations and both are sound; only one of them is a
     * limit of this compiler, and an author who is told nothing has no way to find out which they
     * are looking at.
     */
    public WayToTheBorder wayTo(ModelOccurrence states) {
        List<OnTheWay> found = byComparison.get(states);
        return new WayToTheBorder(found == null ? List.of() : found);
    }

    /**
     * What {@code node} coming out {@code holding} says about this input, and where it says
     * nothing, that.
     *
     * <p>Never empty. Every shape has an answer — a cut where one could be made and a decline
     * where none could — because an empty answer is what made a comparison reached under nothing
     * and one reached past something unreadable into the same reading.
     *
     * <p>One rule for two questions, because they are one question. What reaching the right operand
     * of a condition establishes and what reaching an arm of the fork establishes are both "this
     * subtree came out this way, so what follows" — written apart, the two agreed by having been
     * derived alike, and the day one of them learned to read a new shape of condition would be the
     * day they stopped agreeing.
     *
     * <p>A joined condition that came out the way its connective gives both halves is both halves
     * having come out that way, and which way that is comes from the composition under the outcome
     * rather than from the operator. The other composition says a disjunction of things, which is
     * not a list of cuts and is not approximated into one: {@code A && B} being false says one of
     * them failed and names neither, and narrowing on either would exclude rows that arrive. So it
     * is declined whole, at the condition rather than at an operand — neither operand is what could
     * not be carried.
     */
    static List<OnTheWay> stating(Condition node, InputReading read, boolean holding) {
        return switch (node) {
            // Coming out the way that gives both halves, each of them came out that way too. The
            // other composition says a disjunction of things, which is not a list of cuts and is
            // not approximated into one: `A && B` being false says one of them failed and names
            // neither, and narrowing on either would exclude rows that arrive. So the whole node is
            // declined, at the whole node's place.
            case Condition.Joined joined -> joined.how().under(holding) == ConditionJoin.BOTH
                    ? and(stating(joined.left(), read, holding),
                            stating(joined.right(), read, holding))
                    : List.of(new OnTheWay.Declined(joined.occurrence(), joined.anchor(),
                            new OnTheWay.Why.OneOfTwoThings()));
            case Condition.Compares one -> List.of(of(one, read, holding));
            // A truth is not an inequality over a form, which is what a cut is. Read as one here,
            // the region a search looks in would be narrowed by a proposition this arithmetic
            // cannot state, and the decision a body draws on such a value is a different question
            // asked elsewhere.
            case Condition.Truth truth -> List.of(new OnTheWay.Declined(
                    truth.occurrence(), truth.anchor(), new OnTheWay.Why.NoWordsForTheShape()));
        };
    }

    /**
     * What reaching {@code arm} of {@code match} establishes about this input.
     *
     * <p>Beside {@link #stating} because it is the other half of one question. Both say what a row
     * that got here has already turned out to be; they differ in the vocabulary the answer lands in,
     * and a fork's answer is not a cut — which case a value is has no arithmetic and states nothing
     * about any order.
     *
     * <p><b>The narrowing and never the arm.</b> What a search can compose against is a position
     * read as one of its cases; "the second arm was taken" is a fact about the text. So what is
     * carried is the scrutinee's position with the arm's case on it, and where this reading cannot
     * arrive at one — a scrutinee no position holds, an arm answering for several cases, an arm
     * naming a case that is itself a sum, a case the declarations leave no position at — nothing is
     * invented and the arm is declined.
     *
     * <p>And the narrowing is the one the checker's resolution of the arm settles, taken as it is
     * rather than built again from the case's name: the name says neither whether an optional's
     * present carrier or a sum's case was selected nor how many leaves selecting it covers, and a
     * narrowing spelled the wrong way is a position the reading of the input never holds.
     *
     * <p>Never empty, for the reason {@link #stating} is never empty: an arm that established
     * nothing and an arm nothing could be read of are the two answers a walk has to tell apart, and
     * a silence is both of them.
     */
    static OnTheWay entering(Core.Match match, Core.Case arm, int part, InputDomain inputs,
                             InputReads reads, RuleReadingSource ruleSource,
                             ConditionNumbering numbering) {
        ConditionOccurrence met = numbering.metEntering(match, part);
        ConditionReportAnchor at =
                numbering.anchorOfArm(match.origin(), part, arm.pos(), met);
        Refinement narrowing = arm.selectedCase().map(Refinement::of).orElse(null);
        if (narrowing == null) {
            return new OnTheWay.Declined(met, at,
                    new OnTheWay.Why.ForkArmNotReadAsANarrowing());
        }
        // The arm is declined for either answer: a search composes against a position read as one
        // of its cases, and there is no position to narrow whether the scrutinee stands at none or
        // this reading did not follow it to one.
        TermPath scrutinee = switch (reads.pathOf(match.scrutinee(), ruleSource.newtypes())) {
            case PathResolution.At(var stands) -> stands;
            case PathResolution.NotAPosition _ -> null;
            // And declined for a scrutinee that only may stand at one. What a narrowing is composed
            // against is one position; narrowing each of the ones it may be would say a row
            // reaching this arm stands at a case of every one of them, which is a region narrower
            // than the rows that arrive — the one direction that takes a coverage item away.
            case PathResolution.MayStandAt _ -> null;
        };
        // The position that is narrowed, and not the narrowed one. A case declaring no field has
        // nothing under it and this reading holds no position there, which is what it is for; what
        // has to exist is the position the case is a case of, since that is what a row writes a
        // value at and what a requirement on the way is keyed by.
        //
        // Two values and not one: where the name stands is what the environment answers, and
        // whether the input's rules hold a position there is the reading's.
        if (scrutinee == null || inputs.at(scrutinee) == null) {
            return new OnTheWay.Declined(met, at,
                    new OnTheWay.Why.ForkArmNotReadAsANarrowing());
        }
        return new OnTheWay.Narrowed(at, scrutinee.refine(narrowing));
    }

    /**
     * What reaching arm {@code part} of {@code attempt} establishes about this input, which this
     * reading cannot say.
     *
     * <p>The arm is decided by whether the construction's invariant held of the values it was
     * given, and what that says of the input is the invariant read over those values. That is a
     * reading of the invariant and not of anything this walk met, so the arm is declined rather than
     * given a narrowing the walk did not establish. Declined and not left out: a rule through the
     * arm still turns on it, and it is named so that the success and each departure are distinctions
     * apart.
     *
     * @param at where the arm is written, which is its body since an attempt writes no arm of its own
     */
    static OnTheWay attempting(Core.IfConstructed attempt, int part, SourcePos at,
                               ConditionNumbering numbering) {
        ConditionOccurrence met = numbering.metEntering(attempt, part);
        return new OnTheWay.Declined(met, numbering.anchorOfArm(attempt.origin(), part, at, met),
                new OnTheWay.Why.ForkArmNotReadAsANarrowing());
    }

    /**
     * What {@code comparison} states about this input, coming out {@code holding} — or a decline
     * where the arithmetic reads nothing here.
     *
     * <p>Read once, off the same {@link AffineReading} every other reader of a comparison uses. A
     * second reading of what a comparison says is a second thing to keep in step with how a border
     * is drawn, and the two disagreeing is a region that excludes the very level the border is at.
     *
     * <p><b>Three answers and not one absence.</b> A reading that ran to the end and found the
     * quantity empty, and a reading that stopped, are opposite facts — and both used to arrive here
     * as a {@code null}. The second is not a decline on its own: the arithmetic stopping is what a
     * written value on a carrier that counts nothing does, and such a comparison still says where on
     * that carrier's order the position lies. So the stopped reading is asked again as written, and
     * only a comparison neither vocabulary carries is declined.
     *
     * <p>The reason the same comparison gets for drawing no line is {@link UnreadComparison}'s and
     * answers another question: {@code 1 < 2} is a form nothing reads over there and constrains no
     * position here, and a form this arithmetic cannot carry is a comparison between two positions
     * over there while a relation between two positions is exactly what a cut carries here.
     */
    private static OnTheWay of(Condition.Compares comparison, InputReading read, boolean holding) {
        ConditionReportAnchor at = comparison.anchor();
        return switch (AffineReading.read(comparison.comparison().stated(), read.domain(),
                comparison.reads(), read.rules())) {
            case AffineReading.OfAComparison.Cuts(var affine) -> {
                // What the comparison states, in the words a domain is told things in. Taken the
                // way the path met it: an arm reached by the condition failing has what holds
                // exactly where the comparison does not.
                Rel states = affine.claim().statedRelation();
                // The form with the threshold moved into it, since what a domain is told is
                // `f rel 0`.
                LinearForm<NumericTerm> against =
                        affine.form().minus(LinearForm.constant(affine.cut()));
                Rel met = holding ? states : states.denied();
                // And whether a region can carry it, asked of a region rather than decided from
                // the shape of the form. That a reading reached the end of a comparison is a fact
                // about the arithmetic's reading; whether the values it is over stand on anything
                // a region measures them on is the region's, and the two are not each other — a
                // difference between two positions holding records is read perfectly and is a
                // distance on nothing.
                yield switch (read.quantities().region().assuming(against, met)) {
                    case SearchRegion.Assumption.Taken _ ->
                            new OnTheWay.TakenIn(at, new TakenConstraint.Affine(against, met));
                    case SearchRegion.Assumption.Refused(var why) ->
                            new OnTheWay.Declined(comparison.occurrence(), at, whyDeclined(why));
                };
            }
            // Read from end to end, and the quantity it cuts is nothing. `a - a > 0` constrains no
            // position, so there is nothing for a region to be narrowed by and nothing this
            // compiler fell short of — which is why it is not asked again as written.
            case AffineReading.OfAComparison.CutsNothing _ ->
                    new OnTheWay.Declined(comparison.occurrence(), at,
                            new OnTheWay.Why.ComparisonStatesNoQuantity());
            // The arithmetic stopped, which is what a written value on an order that counts nothing
            // does. Asked as written, and declined only where that reading comes to nothing either.
            case AffineReading.OfAComparison.Stopped _ -> {
                OnTheWay.TakenIn ordered = onAnOrder(comparison, read, holding, at);
                yield ordered != null ? ordered
                        : new OnTheWay.Declined(comparison.occurrence(), at,
                                new OnTheWay.Why.ComparisonNotRepresentedAsACut());
            }
        };
    }

    /**
     * A region's refusal in the words an account of the way is written in.
     *
     * <p>Two vocabularies because they answer to two readers. What a region says is about its own
     * algebra and names the term it has no order for; what an account of the way says is what an
     * author is to make of a condition that narrowed nothing. Written as one, either the region
     * would be naming conditions or the report would be reading terms.
     */
    private static OnTheWay.Why whyDeclined(SearchRegion.Refusal why) {
        return switch (why) {
            case SearchRegion.Refusal.NoOrderUnderATerm _ ->
                    new OnTheWay.Why.QuantityStandsOnNoOrder();
        };
    }

    /**
     * The comparison as a bound on one position's own order, or null where it draws none.
     *
     * <p>Read where the arithmetic stopped and nowhere else, so a spelling never settles what the
     * canonical form has already settled — the arrangement {@link Cutting} is under, reached here
     * for the same reason and off the same reading ({@link ComparedLine#asWritten}). What that
     * reading answers is which position was compared and where on its order the written value
     * falls, which is the whole of an ordered constraint.
     *
     * <p>Taken the way the path met it, like the form above: an arm reached by the condition failing
     * has what holds exactly where the comparison does not. Which is why the relation is settled
     * before the bound is asked for and not after: {@code /= } coming out one way and {@code ==}
     * coming out the other are the same relation, and a reading that looked at what the author
     * wrote would carry one of them and refuse the other.
     *
     * <p>A bound where the relation says where the run stops and a hole where it does not, which
     * are two shapes and not one with a flag: an end moves where a chooser looks, and a hole leaves
     * the run where it was and takes one value out of it.
     */
    private static OnTheWay.TakenIn onAnOrder(Condition.Compares comparison, InputReading read,
                                              boolean holding, ConditionReportAnchor at) {
        ComparedLine drawn = ComparedLine.asWritten(
                comparison.comparison().stated(), read, comparison.reads());
        if (drawn == null) {
            return null;
        }
        Rel states = drawn.claim().statedRelation();
        Rel met = holding ? states : states.denied();
        return new OnTheWay.TakenIn(at, TakenConstraint.Ordered.isABound(met)
                ? new TakenConstraint.Ordered(drawn.term(), drawn.value(), met)
                : new TakenConstraint.AwayFrom(drawn.term(), drawn.value()));
    }

    /** These conditions, with the rule stated at {@code states} reached under {@code assumed}. */
    static final class Collected {

        private final Map<ModelOccurrence, List<OnTheWay>> byComparison = new LinkedHashMap<>();

        void reached(ModelOccurrence states, List<OnTheWay> assumed) {
            // Once per construct of the model, because that is what the walk reads: a comparison
            // inside a non-recursive helper is read once per call of it and each of those calls is
            // a construct of its own. Two arriving under one would be the reading holding two
            // comparisons the model states at one place, which is what nothing downstream could
            // then tell apart — so it is refused here rather than resolved by keeping one of them.
            List<OnTheWay> already = byComparison.putIfAbsent(states, List.copyOf(assumed));
            if (already != null) {
                throw new IllegalStateException(
                        "two comparisons of one reading state one construct of the model: "
                                + states);
            }
        }

        ReachingCuts made() {
            return new ReachingCuts(Lookup.built(put -> byComparison.forEach(put::put)));
        }
    }

    /** What a caller is carrying, with more added, keeping what was already there. */
    private static List<OnTheWay> and(List<OnTheWay> assumed, List<OnTheWay> more) {
        List<OnTheWay> out = new java.util.ArrayList<>(assumed);
        out.addAll(more);
        return List.copyOf(out);
    }

}
