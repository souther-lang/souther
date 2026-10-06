package souther.compiler.partition;

import souther.compiler.check.BooleanMeaning;
import souther.compiler.check.BoundOperationFacts;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.check.StatedComparison;
import souther.compiler.core.Core;
import souther.compiler.inputs.Denotation;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.PathResolution;
import souther.compiler.inputs.ReadMeaning;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.AnswerAspect;
import souther.compiler.semantics.ConditionJoin;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;
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

        /**
         * Nothing to build against, because the answer is the same for every row: it asks nothing
         * of one where that answer is the way asked, and no row comes out of it that way where it
         * is not.
         *
         * <p>Apart from {@link Unread}, which says this reading could not state what is asked. A
         * condition the source settles was read to the end, and taken for one that was not, a way
         * past it would be reported as a way this compiler fell short on.
         */
        record Settled(boolean thisWay) implements Read {}

        /** None, and what stopped it. */
        record Unread(OnTheWay.Why why) implements Read {}
    }

    /** One thing a condition asks, and which condition of the shape asks it. */
    record Stated(Condition where, Read read) {}

    /**
     * What a condition coming out {@code holding} asks of a row, one entry for each thing it asks.
     *
     * <p>A comparison is read as itself, and a value the body asks the truth of as the comparison
     * it means where it means one: an emptiness check is its size against nought, and a denial is
     * what is under it the other way round. That comparison is one no source wrote, which is why it
     * is read here and never named as a condition of the body — what a run through it is seen at is
     * still the application the author wrote.
     */
    static List<Read> of(Condition condition, InputReading read, boolean holding) {
        return stated(condition, read, holding).stream().map(Stated::read).toList();
    }

    /**
     * The same, each with the condition of the shape it was read off — the one a report about it
     * is sent to.
     *
     * <p>A conjunction coming out the way that gives both halves asks both. The other way it says
     * one of two things, and that asks neither — {@code A && B} failing names no half that failed —
     * unless the source settles a half: one that always comes out this way settles the whole, and
     * one that never does leaves the other half as all that is said. Which nodes are conjunctions
     * is {@link Condition#of}'s answer, the one place a condition becomes a shape, and taken as it
     * gave it; and this is the one place what a conjunction asks is composed, so a way on to a
     * border and a predicate asked of each element read one connective one way.
     */
    static List<Stated> stated(Condition condition, InputReading read, boolean holding) {
        return switch (condition) {
            case Condition.Joined joined -> {
                List<Stated> left = stated(joined.left(), read, holding);
                List<Stated> right = stated(joined.right(), read, holding);
                if (joined.how().under(holding) == ConditionJoin.BOTH) {
                    List<Stated> both = new ArrayList<>(left);
                    both.addAll(right);
                    yield List.copyOf(both);
                }
                Settling l = Settling.of(left);
                Settling r = Settling.of(right);
                if (l == Settling.THIS_WAY || r == Settling.THIS_WAY) {
                    yield List.of(new Stated(joined, new Read.Settled(true)));
                }
                if (l == Settling.NEVER) {
                    yield right;
                }
                if (r == Settling.NEVER) {
                    yield left;
                }
                yield List.of(new Stated(joined,
                        new Read.Unread(new OnTheWay.Why.OneOfTwoThings())));
            }
            case Condition.Compares one -> List.of(new Stated(one,
                    ofAComparison(one.comparison().stated(), one.reads(), read, holding)));
            case Condition.Truth truth -> ofATruth(truth.value(), truth.reads(), read, holding,
                    truth.occurrence().behavior()).stream()
                    .map(each -> new Stated(truth, each))
                    .toList();
        };
    }

    /**
     * Whether what was read of a condition is settled for every row.
     *
     * <p>Never where something it asks never comes out the way asked, since all of it is asked at
     * once; the way asked where every part of it always does; and otherwise not settled.
     */
    private enum Settling {
        THIS_WAY, NEVER, OPEN;

        static Settling of(List<Stated> read) {
            boolean every = true;
            for (Stated each : read) {
                if (each.read() instanceof Read.Settled(boolean thisWay)) {
                    if (!thisWay) {
                        return NEVER;
                    }
                } else {
                    every = false;
                }
            }
            return every ? THIS_WAY : OPEN;
        }
    }

    /**
     * What a value the body asks the truth of asks of a row.
     *
     * <p>Bindings and names are looked through on the way down, as {@link Condition#of} looks
     * through them: a denial the library writes as a body binds what it denies, and what it binds
     * is the truth.
     *
     * @param behavior whose body the truth is in, which is whose a predicate handed to an
     *                 operation inside it is
     */
    private static List<Read> ofATruth(Core value, InputReads reads, InputReading read,
                                       boolean holding, String behavior) {
        // Which answers it can give, before what it asks: one the source settles asks nothing of
        // a row, or is a way no row takes, and read for its relations it would be neither — a
        // predicate always holding states no relation of the element, and every element meeting
        // it is not a container holding none. {@link TruthOutcomes} is the one reading of that,
        // which the ways a body is walked are read by too.
        TruthOutcomes.Outcomes outcomes = TruthOutcomes.ofTheTruth(value,
                WhatNamesStandFor.in(reads, read), read.rules().symbols());
        if (outcomes.always(holding) || outcomes.always(!holding)) {
            return List.of(new Read.Settled(outcomes.always(holding)));
        }
        Core e = Core.withoutStanding(value);
        if (e instanceof Core.LetIn let) {
            return ofATruth(let.body(), reads.and(let.binder(), let.value()), read, holding,
                    behavior);
        }
        // It terminates because a binder's value can only mention binders introduced before it.
        if (e instanceof Core.Read name
                && reads.meaningOf(name, read.rules().symbols(), read.rules().newtypes())
                        instanceof ReadMeaning.Through through) {
            return ofATruth(through.denotes().value(), through.denotes().at(), read, holding,
                    behavior);
        }
        Optional<BooleanMeaning.UnderADenial> denied = BooleanMeaning.underADenial(e, holding);
        if (denied.isPresent()) {
            return ofATruth(denied.get().part(), reads, read, denied.get().positive(), behavior);
        }
        List<Read> quantified = ofAQuantifier(e, reads, read, holding, behavior);
        if (quantified != null) {
            return quantified;
        }
        return List.of(BooleanMeaning.asAComparison(e)
                .map(comparison -> ofAComparison(comparison.stated(), reads, read, holding))
                .orElse(new Read.Unread(new OnTheWay.Why.NoWordsForTheShape())));
    }

    /**
     * What a predicate the library says is asked of a container's elements asks of a row, or null
     * where {@code e} applies no such predicate.
     *
     * <p>Which operation asks it of every element and which of one is the library's to say
     * ({@code StatesItsPredicateOfEveryElement}), and the two ways each comes out are two demands
     * and not four: some element meeting the predicate, or every element meeting what it is
     * coming out the way asked. {@code List.any} failing is every element failing its predicate,
     * and {@code List.all} failing is some element failing it.
     *
     * <p>The predicate is read where the closure was written, with what it is handed standing at
     * the container's elements. Neither way round is a relation a region can be narrowed by: a
     * region reads a term inside the elements as the value of one that is there, and what every
     * element meets is met by a container holding none ({@link RowDemand.ForAll}), while what some
     * element meets is met by one element and not the rest ({@link RowDemand.Exists}). Every
     * element meeting a relation about something beside the element is declined, since an empty
     * container meets it whatever that part says.
     */
    private static List<Read> ofAQuantifier(Core e, InputReads reads, InputReading read,
                                            boolean holding, String behavior) {
        AnOperationApplied call = AnOperationApplied.of(e);
        if (call == null) {
            return null;
        }
        ValueName operation = call.operation();
        BoundOperationFacts facts = DefaultBoundOperationFacts.get();
        var container = facts.readsItsContainer(operation);
        var turns = facts.turnsOnWhetherAnArgumentHolds(operation, AnswerAspect.TRUTH);
        Core closure = turns == null ? null : call.argument(turns.argument());
        Core over = container == null ? null : call.argument(container.container());
        if (closure == null || over == null) {
            return null;
        }
        Denotation handed = reads.denotes(closure, read.rules().symbols(),
                read.rules().newtypes());
        if (!(Core.withoutStanding(handed.value()) instanceof Core.Block block)) {
            return null;
        }
        if (!(reads.pathOf(over, read.rules().newtypes())
                instanceof PathResolution.At(TermPath held))) {
            return List.of(new Read.Unread(new OnTheWay.Why.ContainerAtNoPosition()));
        }
        TermPath element = held.element();
        boolean everyElement = facts.statesItsPredicateOfEveryElement(operation) == holding;
        List<Read> out = new ArrayList<>();
        List<RowDemand.Relational> ofTheElement = new ArrayList<>();
        // Named apart from the body's own conditions: nothing reports one of these by its name,
        // and filed under the body's numbering they would take names the body's conditions have.
        Condition predicate = Condition.of(block.body(), handed.at(), read.rules().symbols(),
                read.rules().newtypes(),
                new ConditionNumbering(read.symbols().module(), behavior));
        // Whether what is asked of the element is something no element meets, which leaves every
        // element meeting it to a container holding none and some element meeting it to nothing.
        boolean noElementMeetsIt = false;
        for (Read each : of(predicate, read, holding)) {
            switch (each) {
                case Read.Unread _ -> out.add(each);
                // Met by every element whatever it is, which holds the element to nothing.
                case Read.Settled(boolean thisWay) when thisWay -> { }
                case Read.Settled _ -> noElementMeetsIt = true;
                case Read.Demands(RowDemand.Relational relation)
                        when everyElement && !aboutOnly(relation, element) ->
                        out.add(new Read.Unread(new OnTheWay.Why.MoreThanEachElement()));
                // About the element and nothing beside it, or about some element: what some
                // element meets, the parts of it about nothing of the element hold of the row
                // whichever element it is, so those are relations of the row like any other.
                case Read.Demands(RowDemand.Relational relation)
                        when everyElement || aboutAny(relation, element) ->
                        ofTheElement.add(relation);
                case Read.Demands(RowDemand.Relational _) -> out.add(each);
                // A quantifier inside a quantifier asks of an element's own elements, which is
                // nothing a single relation of the outer element says.
                case Read.Demands(RowDemand.Exists _), Read.Demands(RowDemand.ForAll _) ->
                        out.add(new Read.Unread(new OnTheWay.Why.NoWordsForTheShape()));
            }
        }
        if (everyElement) {
            // Every element meeting what none meets is the container holding none, and nothing
            // else of the predicate is asked of an element that is not there.
            if (noElementMeetsIt) {
                RowDemand.Relational none = sizeAgainst(held, operation, read, false);
                return List.of(none != null ? new Read.Demands(none)
                        : new Read.Unread(new OnTheWay.Why.SizeOfTheContainerNotStated()));
            }
            if (!ofTheElement.isEmpty()) {
                out.add(new Read.Demands(new RowDemand.ForAll(ofTheElement,
                        Optional.ofNullable(sizeAgainst(held, operation, read, false)))));
            }
            // Every element meeting what every element meets, whatever the container holds.
            return out.isEmpty() ? List.of(new Read.Settled(true)) : List.copyOf(out);
        }
        // Some element meeting what none meets is no row's.
        if (noElementMeetsIt) {
            return List.of(new Read.Settled(false));
        }
        Optional<RowDemand.Relational> holdingOne =
                Optional.ofNullable(sizeAgainst(held, operation, read, true));
        // An element meeting nothing this reading could state is still the container holding
        // one, which every row past it does — and where that cannot be said either, it is said
        // that it could not, rather than nothing being asked.
        if (!ofTheElement.isEmpty()) {
            out.add(new Read.Demands(new RowDemand.Exists(ofTheElement, holdingOne)));
        } else {
            out.add(holdingOne.<Read>map(Read.Demands::new)
                    .orElseGet(() -> new Read.Unread(
                            new OnTheWay.Why.SizeOfTheContainerNotStated())));
        }
        return List.copyOf(out);
    }

    /** Whether every term {@code relation} is over stands inside {@code element}. */
    private static boolean aboutOnly(RowDemand.Relational relation, TermPath element) {
        return relation.constraint().terms().stream()
                .allMatch(term -> term.subjectPath().isAtOrUnder(element));
    }

    /** Whether some term {@code relation} is over stands inside {@code element}. */
    private static boolean aboutAny(RowDemand.Relational relation, TermPath element) {
        return relation.constraint().terms().stream()
                .anyMatch(term -> term.subjectPath().isAtOrUnder(element));
    }

    /**
     * That the container at {@code held} holds at least one, or none, as its size against one or
     * against nought — or null where its size is no term of this input or the region cannot
     * carry it.
     *
     * <p>The size is the one the container's own library means by emptiness
     * ({@code MeansTheSameAsASizeOfNought}), asked of the library the quantifier is in: a list is
     * walked by the list's operations, and its size is the list's.
     */
    private static RowDemand.Relational sizeAgainst(TermPath held, ValueName quantifier,
                                                    InputReading read, boolean atLeastOne) {
        if (!(quantifier instanceof ValueName.Stdlib.Operation(String library, String _))) {
            return null;
        }
        BoundOperationFacts facts = DefaultBoundOperationFacts.get();
        for (ValueName emptiness : facts.meansTheSameAsASizeOfNought()) {
            if (!(emptiness instanceof ValueName.Stdlib.Operation(String at, String _))
                    || !at.equals(library)) {
                continue;
            }
            if (!(facts.meansTheSameAsASizeOfNought(emptiness).size().operation()
                    instanceof ValueName.Stdlib size)) {
                return null;
            }
            NumericTerm.TakenOf count = NumericTerm.TakenOf.of(size, held,
                    read.domain().at(held).type(), read.rules().inners(), read.rules().symbols());
            if (count == null) {
                return null;
            }
            // `count - 1 >= 0`, or `count <= 0`.
            LinearForm<NumericTerm> form = atLeastOne
                    ? LinearForm.<NumericTerm>atomMinusConstant(count, ExactRatio.ONE)
                    : LinearForm.<NumericTerm>atom(count);
            Rel rel = atLeastOne ? Rel.GE : Rel.LE;
            return read.quantities().region().assuming(form, rel)
                    instanceof SearchRegion.Assumption.Taken
                    ? new RowDemand.Relational(new TakenConstraint.Affine(form, rel))
                    : null;
        }
        return null;
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
            // position: its two sides differ by the same amount on every row, so it comes out one
            // way for all of them — which asks nothing of a row, or is a way none takes.
            case AffineReading.OfAComparison.CutsNothing constant -> new Read.Settled(
                    constant.holds(comparison.claim().statedRelation()) == holding);
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
