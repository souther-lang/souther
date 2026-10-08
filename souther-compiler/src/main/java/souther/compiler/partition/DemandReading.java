package souther.compiler.partition;

import souther.compiler.check.NumericMeasures;
import souther.compiler.check.StatedComparison;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.ConditionJoin;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * What one condition coming out one way asks of a row, and nothing about where it stood.
 *
 * <p>The reading of a condition and not of a way. Where a condition was met, which construct of the
 * model it is and what a report about it is sent to are the walk's, and a reader that is handed a
 * condition from somewhere that is no way at all — what a quantifier asks of each element — asks
 * this and has none of them to make up. So the answer is a {@link RowDemand} or the reason there is
 * none, and putting it on the way is {@link ReachingCuts}'s.
 *
 * <p><b>What a condition states is not read here.</b> It is the proposition the condition states
 * ({@link Pullback}), and what this does is put that proposition in the words a row is composed in:
 * a relation a region carries, a truth written at a position, a container some or every element of
 * which meets something. What those words cannot carry is said as what stopped it.
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
            case Condition.Compares one -> ofAComparison(one.comparison().stated(), one.reads(),
                    read, holding).stream()
                    .map(each -> new Stated(one, each))
                    .toList();
            case Condition.Truth truth -> projected(holdingAs(Pullback.ofATruth(truth.value(),
                    truth.reads(), read, Optional.empty()).proposition(), holding), read).stream()
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
     * What {@code comparison} coming out {@code holding} asks of a row.
     *
     * <p>Read as what it states ({@link Pullback#ofAComparison}): a size held against a number that
     * parts nought from every size above it asks what the container holding something asks, and
     * any other comparison is the relation it states.
     */
    static List<Read> ofAComparison(StatedComparison comparison, InputReads reads,
                                    InputReading read, boolean holding) {
        return projected(holdingAs(Pullback.ofAComparison(comparison, reads, read,
                Optional.empty()).proposition(), holding), read);
    }

    private static Proposition holdingAs(Proposition stated, boolean holding) {
        return holding ? stated : stated.denied();
    }

    /**
     * What a proposition asks of a row, one entry for each thing it asks.
     *
     * <p>Every part of a conjunction is asked; a disjunction asks one of its parts and names none
     * of them; a relation is asked where a region can carry it, and a truth where it stands at a
     * position. What some element meets, and what every element meets, are asked of the container
     * the elements are in ({@link #ofSomeElement}).
     */
    private static List<Read> projected(Proposition stated, InputReading read) {
        return switch (stated) {
            case Proposition.Always(boolean holds) -> List.of(new Read.Settled(holds));
            case Proposition.Compared compared -> List.of(ofARelation(compared, read));
            case Proposition.Truth(DecisionSubject.AnInput(TermPath at), boolean holds, var _) ->
                    List.of(new Read.Demands(new RowDemand.ATruth(at, holds)));
            case Proposition.Truth _, Proposition.InCases _, Proposition.Present _,
                 Proposition.SameValue _ ->
                    List.of(new Read.Unread(new OnTheWay.Why.NoWordsForTheShape()));
            case Proposition.Unread unread -> List.of(new Read.Unread(
                    new OnTheWay.Why.TheMeaningWasNotRead(unread.why())));
            case Proposition.All all -> {
                List<Read> out = new ArrayList<>();
                all.parts().forEach(part -> out.addAll(projected(part, read)));
                yield List.copyOf(out);
            }
            case Proposition.Any _ -> List.of(new Read.Unread(new OnTheWay.Why.OneOfTwoThings()));
            case Proposition.Some some -> ofSomeElement(some, read);
        };
    }

    /**
     * What some element of a container meeting something — or no element meeting it — asks of a
     * row.
     *
     * <p>No element meeting something is every element meeting its denial, so the two ways round
     * are two demands and not four. Neither is a relation a region can be narrowed by: a region
     * reads a term inside the elements as the value of one that is there, and what every element
     * meets is met by a container holding none ({@link RowDemand.ForAll}), while what some element
     * meets is met by one element and not the rest ({@link RowDemand.Exists}). Every element
     * meeting a relation about something beside the element is declined, since an empty container
     * meets it whatever that part says.
     *
     * <p>The element is what stands at the container's elements — and of a map, at its keys as
     * well, since an entry is its key and its value.
     */
    private static List<Read> ofSomeElement(Proposition.Some some, InputReading read) {
        TermPath held = some.container();
        List<TermPath> element = elementOf(held);
        boolean everyElement = !some.holds();
        Proposition asked = everyElement ? some.ofTheElement().denied() : some.ofTheElement();
        List<Read> out = new ArrayList<>();
        List<RowDemand.OfAnElement> ofTheElement = new ArrayList<>();
        // Whether what is asked of the element is something no element meets, which leaves every
        // element meeting it to a container holding none and some element meeting it to nothing.
        boolean noElementMeetsIt = false;
        List<Proposition> parts = asked instanceof Proposition.All all ? all.parts()
                : List.of(asked);
        for (Proposition part : parts) {
            // What a container holding a value asks of an element is that it be that value, which
            // a composer writes into the container and no region narrows by.
            if (part instanceof Proposition.SameValue(var _, DecisionSubject.AnInput(TermPath at),
                    boolean holds, var _)) {
                ofTheElement.add(holds ? new RowDemand.SameAs(at) : new RowDemand.DifferentFrom(at));
                continue;
            }
            for (Read each : projected(part, read)) {
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
                    // A truth of the element is a value written into one element, which nothing
                    // that composes a container's elements writes.
                    case Read.Demands(RowDemand.ATruth _) ->
                            out.add(new Read.Unread(new OnTheWay.Why.NoWordsForTheShape()));
                }
            }
        }
        if (everyElement) {
            // Every element meeting what none meets is the container holding none, and nothing
            // else of the predicate is asked of an element that is not there.
            if (noElementMeetsIt) {
                RowDemand.Relational none = sizeAgainst(held, read, false);
                return List.of(none != null ? new Read.Demands(none)
                        : new Read.Unread(new OnTheWay.Why.SizeOfTheContainerNotStated()));
            }
            if (!ofTheElement.isEmpty()) {
                out.add(new Read.Demands(new RowDemand.ForAll(held, ofTheElement,
                        Optional.ofNullable(sizeAgainst(held, read, false)))));
            }
            // Every element meeting what every element meets, whatever the container holds.
            return out.isEmpty() ? List.of(new Read.Settled(true)) : List.copyOf(out);
        }
        // Some element meeting what none meets is no row's.
        if (noElementMeetsIt) {
            return List.of(new Read.Settled(false));
        }
        Optional<RowDemand.Relational> holdingOne =
                Optional.ofNullable(sizeAgainst(held, read, true));
        // An element meeting nothing this reading could state is still the container holding
        // one, which every row past it does — and where that cannot be said either, it is said
        // that it could not, rather than nothing being asked.
        if (!ofTheElement.isEmpty()) {
            out.add(new Read.Demands(new RowDemand.Exists(held, ofTheElement, holdingOne)));
        } else {
            out.add(holdingOne.<Read>map(Read.Demands::new)
                    .orElseGet(() -> new Read.Unread(
                            new OnTheWay.Why.SizeOfTheContainerNotStated())));
        }
        return List.copyOf(out);
    }

    /**
     * Where an element of the container at {@code held} stands: at its elements, and at its keys —
     * which only a map has, so of anything else nothing stands there.
     */
    private static List<TermPath> elementOf(TermPath held) {
        return List.of(held.element(), held.key());
    }

    /** Whether every term {@code relation} is over stands inside the element. */
    private static boolean aboutOnly(RowDemand.Relational relation, List<TermPath> element) {
        return relation.constraint().terms().stream().allMatch(term ->
                element.stream().anyMatch(term.subjectPath()::isAtOrUnder));
    }

    /** Whether some term {@code relation} is over stands inside the element. */
    private static boolean aboutAny(RowDemand.Relational relation, List<TermPath> element) {
        return relation.constraint().terms().stream().anyMatch(term ->
                element.stream().anyMatch(term.subjectPath()::isAtOrUnder));
    }

    /**
     * That the container at {@code held} holds at least one, or none, as its size against one or
     * against nought — or null where its size is no term of this input or the region cannot
     * carry it.
     *
     * <p>The size is the one that counts what a value of the container's type holds
     * ({@link NumericMeasures#takenOf}).
     */
    private static RowDemand.Relational sizeAgainst(TermPath held, InputReading read,
                                                    boolean atLeastOne) {
        Type container = read.domain().typeAt(held, read.rules());
        ValueName.Stdlib size = container == null ? null
                : NumericMeasures.takenOf(container, read.rules().inners());
        NumericTerm.TakenOf count = size == null ? null : NumericTerm.TakenOf.of(size, held,
                container, read.rules().inners(), read.rules().symbols());
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

    /**
     * What a relation coming out the way it does asks of a row, where a region can carry it.
     *
     * <p>Whether a region can carry it is asked of a region rather than decided from the shape of
     * the form. That a reading reached the end of a comparison is a fact about the arithmetic's
     * reading; whether the values it is over stand on anything a region measures them on is the
     * region's, and the two are not each other — a difference between two positions holding records
     * is read perfectly and is a distance on nothing.
     *
     * <p>A relation on an order is a bound where the relation says where the run stops and a hole
     * where it does not, which are two shapes and not one with a flag: an end moves where a chooser
     * looks, and a hole leaves the run where it was and takes one value out of it.
     */
    private static Read ofARelation(Proposition.Compared compared, InputReading read) {
        Rel proposition = compared.relation().proposition();
        Rel met = compared.holds() ? proposition : proposition.denied();
        return switch (compared.relation()) {
            case Relation.Affine(LinearForm<Quantity> form, Rel _) -> {
                LinearForm<NumericTerm> against = ofTheInput(form);
                if (against == null) {
                    yield new Read.Unread(new OnTheWay.Why.ComparisonNotRepresentedAsACut());
                }
                yield switch (read.quantities().region().assuming(against, met)) {
                    case SearchRegion.Assumption.Taken _ -> new Read.Demands(
                            new RowDemand.Relational(new TakenConstraint.Affine(against, met)));
                    case SearchRegion.Assumption.Refused(var why) ->
                            new Read.Unread(whyDeclined(why));
                };
            }
            case Relation.Ordered(DecisionAtom.OfTheInput(NumericTerm.FromOnePosition term),
                                  var at, Rel _) ->
                    new Read.Demands(new RowDemand.Relational(TakenConstraint.Ordered.isABound(met)
                            ? new TakenConstraint.Ordered(term, at, met)
                            : new TakenConstraint.AwayFrom(term, at)));
            case Relation.Ordered _ ->
                    new Read.Unread(new OnTheWay.Why.ComparisonNotRepresentedAsACut());
        };
    }

    /** The form over the input's own numbers, or null where it is over anything else — a value
     *  the body bound is one no row writes at. */
    private static LinearForm<NumericTerm> ofTheInput(LinearForm<Quantity> form) {
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        for (Map.Entry<Quantity, ExactRatio> each : form.coefs().entrySet()) {
            if (!(each.getKey() instanceof DecisionAtom.OfTheInput(NumericTerm term))) {
                return null;
            }
            coefs.put(term, each.getValue());
        }
        return new LinearForm<>(form.constant(), coefs);
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
}
