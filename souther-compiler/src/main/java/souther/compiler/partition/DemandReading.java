package souther.compiler.partition;

import souther.compiler.check.NumericMeasures;
import souther.compiler.inputs.Case;
import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.Distinctions;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.meaning.WhyNotTaken;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.ConditionJoin;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;

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

    /**
     * What a condition asks of a row, or why this reading has no words for it.
     *
     * <p>Two halves, and no third. What was taken ({@link Taken}) is the condition said in a row's
     * words, whether or not anything composes a row for it; what was not ({@link Unread}) carries
     * only why the meaning was not read or the words stop. Whether a row was then found, ran, or
     * was shown impossible is the search's answer and is never written here.
     */
    sealed interface Read {

        /** What a condition asks of a row, said in a row's words. */
        sealed interface Taken extends Read {}

        /** A demand a composer can build a row against. */
        record Demands(RowDemand.OfACondition demand) implements Taken {}

        /**
         * Nothing to build against, because the answer is the same for every row: it asks nothing
         * of one where that answer is the way asked, and no row comes out of it that way where it
         * is not.
         *
         * <p>Apart from {@link Unread}, which says this reading could not state what is asked. A
         * condition the source settles was read to the end, and taken for one that was not, a way
         * past it would be reported as a way this compiler fell short on.
         */
        record Settled(boolean thisWay) implements Taken {}

        /**
         * The value at {@code at} being one of {@code cases}: a position read as some of its
         * cases, which a composer writes and the walk carries as a narrowing.
         */
        record Narrows(TermPath at, CasesLeft cases) implements Taken {

            public Narrows {
                if (at == null || cases == null) {
                    throw new IllegalArgumentException("a position is read as some of its cases");
                }
            }
        }

        /**
         * One of several things, each asked whole: a row is past the condition where it meets
         * every demand of one alternative, and an alternative is no less a way for the others
         * beside it.
         *
         * @param alternatives what each alternative asks, each once and in the order the parts are
         *                     kept; two or more, since one is no choice
         */
        record OneOf(List<List<Read>> alternatives) implements Taken {

            public OneOf {
                alternatives = alternatives.stream().map(List::copyOf).distinct().toList();
                if (alternatives.size() < 2) {
                    throw new IllegalArgumentException("one of several things is two or more: "
                            + alternatives);
                }
            }
        }

        /** None, and everything that stopped it, each once. */
        record Unread(List<WhyNotTaken> whys) implements Read {

            Unread(WhyNotTaken why) {
                this(List.of(why));
            }

            public Unread {
                whys = List.copyOf(new LinkedHashSet<>(whys));
                if (whys.isEmpty()) {
                    throw new IllegalArgumentException("what stopped a condition is something");
                }
            }
        }
    }

    /** {@code stated}, read to the end, asked of a row as a statement only the run decides. */
    private static Read forTheRun(Proposition stated, RowDemand.NoComposer why) {
        return new Read.Demands(new RowDemand.ForTheRun(stated, why));
    }

    /** What a dependency answered, which a row stands in rather than writes. */
    private static Read.Unread anAnswerARowStandsIn() {
        return new Read.Unread(new WhyNotTaken.OutsideDomain(
                WhyNotTaken.DomainLimit.AN_ANSWER_A_ROW_STANDS_IN));
    }

    private static Read.Unread aSizeNothingMeasures() {
        return new Read.Unread(new WhyNotTaken.OutsideDomain(
                WhyNotTaken.DomainLimit.A_SIZE_NOTHING_MEASURES));
    }

    /** One thing a condition asks, and which condition of the shape asks it. */
    record Stated(Condition where, Read read) {}

    /**
     * What a condition coming out {@code holding} asks of a row, one entry for each thing it asks,
     * each with the condition of the shape it was read off — the one a report about it is sent to.
     *
     * <p>A conjunction coming out the way that gives both halves asks both. The other way it says
     * one of two things, and that asks neither — {@code A && B} failing names no half that failed —
     * unless the source settles a half: one that always comes out this way settles the whole, and
     * one that never does leaves the other half as all that is said. Which nodes are conjunctions
     * is {@link Condition#of}'s answer, the one place a condition becomes a shape, and taken as it
     * gave it; and this is the one place what a conjunction asks is composed, so a way on to a
     * border and a predicate asked of each element read one connective one way.
     *
     * @param conditions what each part states, read once for every reader of the same reading
     */
    static List<Stated> stated(Condition condition, InputReading read, boolean holding,
                               WhatConditionsState conditions) {
        return switch (condition) {
            case Condition.Joined joined -> {
                List<Stated> left = stated(joined.left(), read, holding, conditions);
                List<Stated> right = stated(joined.right(), read, holding, conditions);
                if (joined.how().under(holding) == ConditionJoin.BOTH) {
                    yield List.copyOf(both(left, right));
                }
                yield oneOf(List.of(left, right), Stated::read, each -> new Stated(joined, each));
            }
            // What a comparison states, read as what it states: a size held against a number that
            // parts nought from every size above it asks what the container holding something
            // asks, and any other comparison is the relation it states.
            case Condition.Compares one -> projected(holdingAs(conditions.comparison(
                    one.comparison().stated(), one.reads(), read).stated().proposition(),
                    holding), read).stream()
                    .map(each -> new Stated(one, each))
                    .toList();
            case Condition.Truth truth -> projected(holdingAs(conditions.truth(truth.value(),
                    truth.reads(), read).proposition(), holding), read).stream()
                    .map(each -> new Stated(truth, each))
                    .toList();
        };
    }

    /**
     * What {@code condition} coming out true states, whole, as the one reading of a truth reads it.
     *
     * @param conditions what each part states, read once for every reader of the same reading
     */
    static Proposition statedBy(Condition condition, InputReading read,
                                WhatConditionsState conditions) {
        return switch (condition) {
            case Condition.Joined joined ->
                    conditions.truth(joined.value(), joined.reads(), read).proposition();
            case Condition.Compares one -> conditions.comparison(one.comparison().stated(),
                    one.reads(), read).stated().proposition();
            case Condition.Truth truth ->
                    conditions.truth(truth.value(), truth.reads(), read).proposition();
        };
    }

    private static List<Stated> both(List<Stated> left, List<Stated> right) {
        List<Stated> out = new ArrayList<>(left);
        out.addAll(right);
        return out;
    }

    /**
     * What one of several things asks, each given as everything it asks — the one rule for a
     * disjunction, however it was written, so a condition written with {@code ||} and the same
     * condition written as a denied conjunction say the same.
     *
     * <p>Settled where one of them always comes out the way asked, and the one left where every
     * other never does — or where every other asks the same as it. Otherwise each that could be
     * what holds is one alternative ({@link Read.OneOf}); one that never comes out the way asked is
     * none.
     *
     * @param readOf what an entry of a part is read as
     * @param asWhole an entry standing for what the whole asks
     */
    private static <T> List<T> oneOf(List<List<T>> parts, Function<T, Read> readOf,
                                     Function<Read, T> asWhole) {
        List<List<Read>> open = new ArrayList<>();
        List<T> lastOpen = parts.getLast();
        for (List<T> part : parts) {
            List<Read> asked = part.stream().map(readOf).toList();
            switch (Settling.of(asked)) {
                case THIS_WAY -> {
                    return List.of(asWhole.apply(new Read.Settled(true)));
                }
                case NEVER -> { }
                case OPEN -> {
                    open.add(asked);
                    lastOpen = part;
                }
            }
        }
        return open.stream().distinct().count() <= 1 ? lastOpen
                : List.of(asWhole.apply(new Read.OneOf(open)));
    }

    /**
     * Whether what was read of a condition is settled for every row.
     *
     * <p>Never where something it asks never comes out the way asked, since all of it is asked at
     * once; the way asked where every part of it always does; and otherwise not settled.
     */
    private enum Settling {
        THIS_WAY, NEVER, OPEN;

        static Settling of(List<Read> read) {
            boolean every = true;
            for (Read each : read) {
                if (each instanceof Read.Settled(boolean thisWay)) {
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
     * What {@code stated} asks of a row, one entry for each thing it asks — a proposition no
     * condition of the shape states, such as where a line of a statement of several decides.
     */
    static List<Read> asked(Proposition stated, InputReading read) {
        return projected(stated, read);
    }

    /**
     * What an element of {@code count}'s container is held to where it meets what is counted, as
     * the relations a region is narrowed by: the reading a condition that some element meets it
     * comes to.
     *
     * @return empty where what is counted is no relations about the element and the numbers beside
     *         it alone — a statement over another container's elements, or one an element meets
     *         one of several ways
     */
    static Optional<List<TakenConstraint>> anElementMeeting(Quantity.HowManyMeet count,
                                                            InputReading read) {
        List<Read> reads = asked(count.someMeets(), read);
        if (reads.size() != 1
                || !(reads.getFirst() instanceof Read.Demands(RowDemand.Exists exists))
                || exists.relations().size() != exists.ofAnElement().size()) {
            return Optional.empty();
        }
        return Optional.of(exists.relations().stream()
                .map(RowDemand.Relational::constraint).toList());
    }

    /**
     * The value at {@code at} being none of {@code cases}: one of the others its type divides into
     * ({@link Distinctions#ofType}), which no row is where there are none.
     */
    private static Read notOfItsCases(TermPath at, CasesLeft cases, InputReading read) {
        Position position = read.domain().at(at.position());
        if (position == null) {
            return new Read.Unread(new WhyNotTaken.OutsideDomain(
                    WhyNotTaken.DomainLimit.A_POSITION_THE_READING_HOLDS_NO_PLACE_FOR));
        }
        List<Refinement> others = new ArrayList<>();
        for (Case each : Distinctions.ofType(position.view().shape(), read.rules().symbols(),
                read.rules().kinds(), read.rules().sums())) {
            Refinement one = Refinement.of(each);
            if (one != null && !cases.atoms().contains(one)) {
                others.add(one);
            }
        }
        CasesLeft left = CasesLeft.ofEach(others);
        return left == null ? new Read.Settled(false) : new Read.Narrows(at, left);
    }

    private static Proposition holdingAs(Proposition stated, boolean holding) {
        return holding ? stated : stated.denied();
    }

    /**
     * What a proposition asks of a row, one entry for each thing it asks.
     *
     * <p>Every part of a conjunction is asked; a disjunction is asked as {@link #oneOf} asks one
     * written with {@code ||}; a relation is asked where a region can carry it, and a truth where
     * it stands at a position. What some element meets, and what every element meets, are asked of the container
     * the elements are in ({@link #ofSomeElement}).
     */
    private static List<Read> projected(Proposition stated, InputReading read) {
        return switch (stated) {
            case Proposition.Always(boolean holds) -> List.of(new Read.Settled(holds));
            case Proposition.Compared compared -> List.of(ofARelation(compared, read));
            case Proposition.Truth(DecisionSubject.AnInput(TermPath at), boolean holds, var _) ->
                    List.of(new Read.Demands(new RowDemand.ATruth(at, holds)));
            case Proposition.Truth(DecisionSubject.AnAnswer _, boolean _, var _),
                 Proposition.InCases(DecisionSubject.AnAnswer _, var _, boolean _, var _),
                 Proposition.Present(DecisionSubject.AnAnswer _, boolean _, var _) ->
                    List.of(anAnswerARowStandsIn());
            case Proposition.InCases(DecisionSubject.AnInput(TermPath at), CasesLeft cases,
                                     boolean holds, var _) ->
                    List.of(holds ? new Read.Narrows(at, cases) : notOfItsCases(at, cases, read));
            // Holding a value or holding none is which of an optional's two carriers stands there.
            case Proposition.Present(DecisionSubject.AnInput(TermPath at), boolean holds, var _) ->
                    List.of(new Read.Narrows(at,
                            CasesLeft.of(Refinement.of(new Case.Presence(holds)))));
            case Proposition.SameValue _ ->
                    List.of(forTheRun(stated, RowDemand.NoComposer.TWO_SUBJECTS_ONE_VALUE));
            case Proposition.Unread unread -> List.of(new Read.Unread(
                    new WhyNotTaken.MeaningUnread(unread.why())));
            case Proposition.All all -> {
                List<Read> out = new ArrayList<>();
                all.parts().forEach(part -> out.addAll(projected(part, read)));
                yield List.copyOf(out);
            }
            case Proposition.Any any -> oneOf(any.parts().stream()
                    .map(part -> projected(part, read)).toList(), each -> each, each -> each);
            // One of several statements, which one turning on which application a run meets the
            // condition on: one alternative per statement that can hold, as a disjunction is. A
            // statement of an application no run makes is an alternative too many and never one
            // too few, so a row is held to none of them alone — and one that holds of every row
            // settles nothing, since the application may not be one a run makes.
            case Proposition.OnAnApplication applications -> {
                List<List<Read>> open = new ArrayList<>();
                for (Proposition each : applications.each()) {
                    List<Read> asked = projected(each, read);
                    if (Settling.of(asked) != Settling.NEVER) {
                        open.add(asked);
                    }
                }
                yield switch ((int) open.stream().distinct().count()) {
                    case 0 -> List.of(new Read.Settled(false));
                    case 1 -> open.getFirst();
                    default -> List.of(new Read.OneOf(open));
                };
            }
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
        // The first kind of part asked of the element that no composer writes toward, for which
        // the whole is asked of the run beside what the rest asks.
        RowDemand.NoComposer uncomposed = null;
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
                RowDemand.NoComposer writtenByNoComposer = switch (each) {
                    case Read.Unread _ -> {
                        out.add(each);
                        yield null;
                    }
                    // Met by every element whatever it is, which holds the element to nothing.
                    case Read.Settled(boolean thisWay) when thisWay -> null;
                    case Read.Settled _ -> {
                        noElementMeetsIt = true;
                        yield null;
                    }
                    // Every element meeting a relation about more than the element: a container
                    // holding none meets it whatever the rest says, and a composer writes the
                    // elements apart from the numbers beside them.
                    case Read.Demands(RowDemand.Relational relation)
                            when everyElement && !aboutOnly(relation, element) ->
                            RowDemand.NoComposer.EVERY_ELEMENT_AND_MORE;
                    // About the element and nothing beside it, or about some element: what some
                    // element meets, the parts of it about nothing of the element hold of the row
                    // whichever element it is, so those are relations of the row like any other.
                    case Read.Demands(RowDemand.Relational relation)
                            when everyElement || aboutAny(relation, element) -> {
                        ofTheElement.add(relation);
                        yield null;
                    }
                    case Read.Demands(RowDemand.Relational _) -> {
                        out.add(each);
                        yield null;
                    }
                    // A quantifier inside a quantifier asks of an element's own elements, which is
                    // nothing a single relation of the outer element says.
                    case Read.Demands(RowDemand.Exists _), Read.Demands(RowDemand.ForAll _),
                         Read.Demands(RowDemand.SoMany _) ->
                            RowDemand.NoComposer.A_QUANTIFIER_WITHIN_ONE;
                    // A truth or a case of the element is a value written into one element, which
                    // nothing that composes a container's elements writes.
                    case Read.Demands(RowDemand.ATruth _), Read.Narrows _ ->
                            RowDemand.NoComposer.A_TRUTH_OF_AN_ELEMENT;
                    case Read.Demands(RowDemand.ForTheRun(var _, var why)) -> why;
                    case Read.OneOf _ -> RowDemand.NoComposer.ONE_OF_SEVERAL_FOR_AN_ELEMENT;
                };
                if (uncomposed == null) {
                    uncomposed = writtenByNoComposer;
                }
            }
        }
        // What some or every element meets, asked of the run where a part of it is one no
        // composer writes; the parts a composer does write are still asked, which every row past
        // the whole meets.
        if (uncomposed != null) {
            out.add(forTheRun(some, uncomposed));
        }
        if (everyElement) {
            // Every element meeting what none meets is the container holding none, and nothing
            // else of the predicate is asked of an element that is not there.
            if (noElementMeetsIt) {
                RowDemand.Relational none = sizeAgainst(held, read, false);
                return List.of(none != null ? new Read.Demands(none) : aSizeNothingMeasures());
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
                    .orElseGet(DemandReading::aSizeNothingMeasures));
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
            // How many elements meet a statement against a number, which is no number a row
            // writes and is composed for: the count is held against the one number the form
            // weighs it against, and its weight is above nought, as a relation's first weight is.
            case Relation.Affine affine
                    when AStatementAtARow.countIn(affine) instanceof Quantity.HowManyMeet count
                    && AStatementAtARow.askable(count.ofTheElement()) -> {
                ExactRatio weight = affine.form().coefs().values().iterator().next();
                yield affine.form().constant().negated().dividedBy(weight)
                        instanceof ExactAnswer.Held<ExactRatio>(ExactRatio level)
                        ? new Read.Demands(new RowDemand.SoMany(count, met, level,
                                anElementMeeting(count, read)))
                        : forTheRun(compared, RowDemand.NoComposer.A_COUNT_AGAINST_A_NUMBER_NOT_HELD);
            }
            case Relation.Affine(LinearForm<Quantity> form, Rel _) -> {
                LinearForm<NumericTerm> against = WhatTheRulesLeave.ofTheInput(form);
                if (against == null) {
                    yield overNoRowNumber(compared, form);
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
            case Relation.Ordered(DecisionAtom.OfAnAnswer _, var _, Rel _) -> anAnswerARowStandsIn();
            case Relation.Ordered _ ->
                    forTheRun(compared, RowDemand.NoComposer.AN_ORDER_OF_NO_ONE_POSITION);
        };
    }

    /**
     * What a relation over {@code form}, which is over some number no row writes, asks of a row.
     *
     * <p>What a dependency answered is no number a row writes, and is said as that. Otherwise the
     * relation is asked of the run: a value the body works out, or how many elements meet
     * something, is a number a row comes to and not one it writes, and only the count has a
     * composer at all — for a count alone against a number, which this is not.
     */
    private static Read overNoRowNumber(Proposition.Compared compared, LinearForm<Quantity> form) {
        boolean counted = false;
        for (Quantity atom : form.coefs().keySet()) {
            switch (atom) {
                case DecisionAtom.OfAnAnswer _ -> {
                    return anAnswerARowStandsIn();
                }
                case Quantity.HowManyMeet _, Quantity.HowManyHold _ -> counted = true;
                case DecisionAtom.OfTheInput _, Quantity.OfABinding _ -> { }
            }
        }
        return forTheRun(compared, counted ? RowDemand.NoComposer.A_COUNT_OF_ELEMENTS
                : RowDemand.NoComposer.A_VALUE_THE_BODY_WORKS_OUT);
    }

    /**
     * A region's refusal in the words an account of the way is written in.
     *
     * <p>Two vocabularies because they answer to two readers. What a region says is about its own
     * algebra and names the term it has no order for; what an account of the way says is what an
     * author is to make of a condition that narrowed nothing. Written as one, either the region
     * would be naming conditions or the report would be reading terms.
     */
    private static WhyNotTaken whyDeclined(SearchRegion.Refusal why) {
        return switch (why) {
            case SearchRegion.Refusal.NoOrderUnderATerm _ ->
                    new WhyNotTaken.OutsideDomain(WhyNotTaken.DomainLimit.A_QUANTITY_ON_NO_ORDER);
        };
    }
}
