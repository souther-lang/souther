package souther.compiler.partition;

import souther.compiler.check.BooleanMeaning;
import souther.compiler.check.StatedComparison;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.ReadMeaning;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.Optional;

/**
 * What one condition coming out one way asks of a row, and nothing about where it stood.
 *
 * <p>The reading of a condition and not of a way. Where a condition was met, which construct of the
 * model it is and what a report about it is sent to are the walk's, and a reader that is handed a
 * condition from somewhere that is no way at all — what a quantifier asks of each element — asks
 * this and has none of them to make up. So the answer is a {@link RowDemand} or the reason there is
 * none, and putting it on the way is {@link ReachingCuts}'s.
 */
final class DemandReading {

    private DemandReading() {
    }

    /** What a condition asks of a row, or why this reading has no words for it. */
    sealed interface Read {

        /** A demand a composer can build a row against. */
        record Demands(RowDemand.OfACondition demand) implements Read {}

        /** None, and what stopped it. */
        record Unread(OnTheWay.Why why) implements Read {}
    }

    /**
     * What a value the body asks the truth of states, coming out {@code holding}.
     *
     * <p>The comparison it means where it means one, read as that comparison is: an emptiness check
     * is its size against nought, and a denial is the comparison under it the other way round. The
     * comparison is one no source wrote where the truth is an operation's answer, which is why it is
     * read here and never named as a condition of the body — what a run through it is seen at is
     * still the application the author wrote.
     *
     * <p>Bindings and names are looked through on the way down, as {@link Condition#of} looks
     * through them: a denial the library writes as a body binds what it denies, and what it binds
     * is the truth.
     */
    static Read ofATruth(Core value, InputReads reads, InputReading read, boolean holding) {
        Core e = Core.withoutStanding(value);
        if (e instanceof Core.LetIn let) {
            return ofATruth(let.body(), reads.and(let.binder(), let.value()), read, holding);
        }
        // It terminates because a binder's value can only mention binders introduced before it.
        if (e instanceof Core.Read name
                && reads.meaningOf(name, read.rules().symbols(), read.rules().newtypes())
                        instanceof ReadMeaning.Through through) {
            return ofATruth(through.denotes().value(), through.denotes().at(), read, holding);
        }
        Optional<BooleanMeaning.UnderADenial> denied = BooleanMeaning.underADenial(e, holding);
        if (denied.isPresent()) {
            return ofATruth(denied.get().part(), reads, read, denied.get().positive());
        }
        return BooleanMeaning.asAComparison(e)
                .map(comparison -> ofAComparison(comparison.stated(), reads, read, holding))
                .orElse(new Read.Unread(new OnTheWay.Why.NoWordsForTheShape()));
    }

    /**
     * What {@code comparison} states about this input, coming out {@code holding} — or why the
     * arithmetic reads nothing here.
     *
     * <p>Read once, off the same {@link AffineReading} every other reader of a comparison uses. A
     * second reading of what a comparison says is a second thing to keep in step with how a border
     * is drawn, and the two disagreeing is a region that excludes the very level the border is at.
     *
     * <p><b>Three answers and not one absence.</b> A reading that ran to the end and found the
     * quantity empty, and a reading that stopped, are opposite facts. The second is not a decline
     * on its own: the arithmetic stopping is what a written value on a carrier that counts nothing
     * does, and such a comparison still says where on that carrier's order the position lies. So
     * the stopped reading is asked again as written, and only a comparison neither vocabulary
     * carries is declined.
     *
     * <p>The reason the same comparison gets for drawing no line is {@link UnreadComparison}'s and
     * answers another question: {@code 1 < 2} is a form nothing reads over there and constrains no
     * position here, and a form this arithmetic cannot carry is a comparison between two positions
     * over there while a relation between two positions is exactly what a cut carries here.
     */
    static Read ofAComparison(StatedComparison comparison, InputReads reads, InputReading read,
                              boolean holding) {
        return switch (AffineReading.read(comparison, read.domain(), reads, read.rules())) {
            case AffineReading.OfAComparison.Cuts(var affine) -> {
                // What the comparison states, in the words a domain is told things in. Taken the
                // way the path met it: an arm reached by the condition failing has what holds
                // exactly where the comparison does not.
                Rel states = affine.claim().statedRelation();
                // The form with the threshold moved into it, since what a domain is told is
                // `f rel 0`.
                LinearForm<NumericTerm> against =
                        affine.form().minus(LinearForm.constant(affine.cut())).orNull();
                // A form no ratio holds once the threshold is moved into it is a comparison this
                // cannot state to a region, which is a comparison not represented as a cut.
                if (against == null) {
                    yield new Read.Unread(new OnTheWay.Why.ComparisonNotRepresentedAsACut());
                }
                Rel met = holding ? states : states.denied();
                // And whether a region can carry it, asked of a region rather than decided from
                // the shape of the form. That a reading reached the end of a comparison is a fact
                // about the arithmetic's reading; whether the values it is over stand on anything
                // a region measures them on is the region's, and the two are not each other — a
                // difference between two positions holding records is read perfectly and is a
                // distance on nothing.
                yield switch (read.quantities().region().assuming(against, met)) {
                    case SearchRegion.Assumption.Taken _ -> new Read.Demands(
                            new RowDemand.Relational(new TakenConstraint.Affine(against, met)));
                    case SearchRegion.Assumption.Refused(var why) ->
                            new Read.Unread(whyDeclined(why));
                };
            }
            // Read from end to end, and the quantity it cuts is nothing. `a - a > 0` constrains no
            // position, so there is nothing for a region to be narrowed by and nothing this
            // compiler fell short of — which is why it is not asked again as written.
            case AffineReading.OfAComparison.CutsNothing _ ->
                    new Read.Unread(new OnTheWay.Why.ComparisonStatesNoQuantity());
            // Read from end to end and the difference of the two sides has no number to state to a
            // region. Nothing is narrowed by it, and nothing was left unread — so it is not asked
            // again as written, which is a reading of a spelling and would say nothing more.
            case AffineReading.OfAComparison.NotHeld _ ->
                    new Read.Unread(new OnTheWay.Why.ComparisonNotRepresentedAsACut());
            // The arithmetic stopped, which is what a written value on an order that counts nothing
            // does. Asked as written, and declined only where that reading comes to nothing either.
            case AffineReading.OfAComparison.Stopped _ -> {
                TakenConstraint ordered = onAnOrder(comparison, reads, read, holding);
                yield ordered != null ? new Read.Demands(new RowDemand.Relational(ordered))
                        : new Read.Unread(new OnTheWay.Why.ComparisonNotRepresentedAsACut());
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
    private static TakenConstraint onAnOrder(StatedComparison comparison, InputReads reads,
                                             InputReading read, boolean holding) {
        ComparedLine drawn = ComparedLine.asWritten(comparison, read, reads);
        if (drawn == null) {
            return null;
        }
        Rel states = drawn.claim().statedRelation();
        Rel met = holding ? states : states.denied();
        return TakenConstraint.Ordered.isABound(met)
                ? new TakenConstraint.Ordered(drawn.term(), drawn.value(), met)
                : new TakenConstraint.AwayFrom(drawn.term(), drawn.value());
    }
}
