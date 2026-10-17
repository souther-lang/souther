package souther.compiler.check;

import souther.compiler.inputs.AnEvaluation;
import souther.compiler.inputs.Case;
import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.NumericTerms;
import souther.compiler.core.Core;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.meaning.WhyNotTaken;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.OrderedInterval;
import souther.compiler.numeric.OrderedIntervals;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Rel;
import souther.compiler.numeric.WholeNumberRuns;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.semantics.Arithmetic;
import souther.compiler.semantics.ConstantArguments;
import souther.compiler.semantics.ResultRange;
import souther.compiler.semantics.TakenArguments;
import souther.compiler.semantics.TakenAs;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;
import souther.compiler.values.AdmittedPlan;
import souther.compiler.values.Allowance;
import souther.compiler.values.PlannedValues;
import souther.compiler.values.ValueSet;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.EnumSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;

/**
 * What a path knows once a condition comes out a way, read off what the condition states.
 *
 * <p>The condition's meaning is not read here. It is the proposition the condition states, read
 * once off the tree where the language's operations stand ({@link Proposition}); what this does is
 * take into {@link Known} every fact the proposition coming out that way makes certain and that
 * {@code Known} can hold, and nothing else. So what a path knows is never more than the condition
 * says, and how much of it is known is this reader's reach and not a second reading of the
 * condition.
 *
 * <p><b>What is taken.</b> A comparison over numbers of the input — a value at a position, the size
 * of a container at one — as the relation it states. A value of the input against a written place
 * on its order, as the range it leaves the value. A truth at a position. Both halves of a
 * conjunction, since both hold. Of a disjunction, the one part what is known leaves, or nothing
 * reached where it leaves none; and of one between comparisons of one whole number, the values of
 * it the comparisons leave. That some element meets something, as the container holding one.
 * Which cases a value may be, and whether an optional holds one. Nothing at all where the
 * condition is never met, since nothing reaches there.
 *
 * <p><b>What is not.</b> Which of several parts of a disjunction holds, where what is known leaves
 * more than one; which element meets something; what every element meets, which a path holds
 * only as the closure it was written with; a value being none of some cases, two values being one,
 * a value being other than a place on its order, a count of elements, a place this tree does not read, and a part nothing
 * read. Each is left out with the limit of {@link Known} it meets, which is the sound answer with
 * less: a path that took nothing in has ruled nothing out. And one of several things whose parts,
 * counted with every disjunction inside them, come to more than one reading of a condition takes
 * alone is left out for that figure, and not for a limit of {@code Known}.
 */
final class MeaningAssumptions {

    /**
     * Where the positions a proposition names stand in the tree a reader walks.
     *
     * <p>A position that is a chain of fields from a parameter stands there whatever is in force.
     * One under a narrowing or inside a container stands where the walk's own tree reads it — a
     * name an arm bound, an element a closure was handed — so it is found among what the condition
     * itself reads, and the value is the one that expression names.
     *
     * @param parameters the binding each parameter of the behavior is, by the name a position's
     *                   path starts with
     * @param typeAt     what stands at a position, or null where nothing is known to
     * @param standing   the expression of the condition that reads each position, in the tree the
     *                   reader walks
     * @param answering  the expression of the condition that is each place in an answer a
     *                   dependency gave, in the tree the reader walks: the call, or a name it was
     *                   given, with the fields read off it
     */
    record InputPlaces(Map<String, BindingId> parameters, Function<TermPath, Type> typeAt,
                       Map<TermPath, Core> standing, Map<AnswerPlace, Core> answering) {

        /** Where nothing stands: no proposition names a place here. */
        static final InputPlaces NONE =
                new InputPlaces(Map.of(), path -> null, Map.of(), Map.of());

        InputPlaces {
            standing = Map.copyOf(standing);
            answering = Map.copyOf(answering);
        }

        /** The same places, with what a condition reads standing at each position it reads and
         *  each place in an answer it reads. */
        InputPlaces readBy(Map<TermPath, Core> condition, Map<AnswerPlace, Core> answers) {
            return new InputPlaces(parameters, typeAt, condition, answers);
        }
    }

    /**
     * A place in what one evaluation of a dependency answered: the evaluation, and the fields read
     * off it in the order they are written.
     *
     * <p>What a proposition about an answer and the tree a reader walks agree on. The arguments the
     * call was handed are not part of it: they are what the evaluation was asked, and the evaluation
     * says which call it is.
     */
    record AnswerPlace(AnEvaluation evaluation, List<TermPath.Step> steps) {

        AnswerPlace {
            steps = List.copyOf(steps);
        }
    }

    private final Terms terms;
    private final InputPlaces places;
    /** What the bindings in force where the condition stands are, which is where a value the body
     *  bound is found. */
    private final Denotations at;
    private Known known;
    private boolean taken;
    /** Why each part of what was stated that a path does not hold was not taken in; empty where
     *  every part is one a path holds. */
    private final List<WhyNotTaken> notTaken = new ArrayList<>();
    /** How many more parts of a disjunction this reading takes alone, shared by every part taken
     *  alone inside another. */
    private final Tries tries;

    private MeaningAssumptions(Terms terms, InputPlaces places, Denotations at, Known known,
                               Tries tries) {
        this.terms = terms;
        this.places = places;
        this.at = at;
        this.known = known;
        this.tries = tries;
    }

    /**
     * How many parts of a disjunction one reading of a condition takes alone
     * ({@link CompositionBudget#ALTERNATIVES_A_PATH_TRIES}).
     *
     * <p>One count for the whole reading and not one per disjunction. A part taken alone holds
     * disjunctions of its own, each of whose parts is taken alone again, so what grows is the
     * nesting: a disjunction of two parts never reaches a count kept for it alone, however many
     * times over the nesting takes it.
     */
    private static final class Tries {

        private int left = CompositionBudget.ALTERNATIVES_A_PATH_TRIES.maximum();

        /** Whether another part may be taken alone, counting it where it may. */
        boolean another() {
            if (left == 0) {
                return false;
            }
            left--;
            return true;
        }
    }

    /** What {@code k} comes to once what {@code stated} states comes out {@code positive}, read
     *  where the bindings {@code at} holds are in force. */
    static Predicates.Assumed assumed(Proposition stated, boolean positive, Known k, Terms terms,
                                      InputPlaces places, Denotations at) {
        Proposition asked = positive ? stated : stated.denied();
        MeaningAssumptions taking = new MeaningAssumptions(terms, places, at, k, new Tries());
        taking.take(asked);
        // Read to the end only where every part was taken in: a part a path cannot hold leaves an
        // arm under it unsettled for this reader's reach, which is not a fact about the model.
        return new Predicates.Assumed(taking.known, taking.taken, taking.notTaken.isEmpty(),
                taking.notTaken);
    }

    private void notTaken(WhyNotTaken why) {
        notTaken.add(why);
    }

    private void outside(WhyNotTaken.DomainLimit limit) {
        notTaken(new WhyNotTaken.OutsideDomain(limit));
    }

    private void take(Proposition asked) {
        switch (asked) {
            case Proposition.Always(boolean holds) when !holds -> {
                known = known.reachingNothing();
                taken = true;
            }
            case Proposition.All all -> all.parts().forEach(this::take);
            case Proposition.Compared(Relation.Affine(LinearForm<Quantity> form, Rel p),
                                      boolean holds, var _) -> {
                switch (formAt(form)) {
                    case FormAt.Named(LinearForm<FactSubject> over) -> {
                        known = known.taking(over, holds ? p : p.denied(),
                                Known.Held.ON_THE_PATH, terms.kindsOf(over));
                        taken = true;
                    }
                    case FormAt.Unnamed(Set<WhyNotTaken.DomainLimit> edges) ->
                            edges.forEach(this::outside);
                }
            }
            case Proposition.Truth(DecisionSubject.AnInput(TermPath at), boolean holds, var _) -> {
                FactSubject place = placeOf(at);
                if (place != null) {
                    known = known.taking(place, holds, Known.Held.ON_THE_PATH);
                    taken = true;
                } else {
                    outside(WhyNotTaken.DomainLimit.A_PLACE_THE_PATH_DOES_NOT_READ);
                }
            }
            case Proposition.Always _ -> { }
            case Proposition.Any any -> takingOneOf(any);
            // Which application is no fact of a path.
            case Proposition.OnAnApplication _ ->
                    WhyNotTaken.declinedWhole(new WhyNotTaken.OutsideDomain(
                            WhyNotTaken.DomainLimit.A_PATH_KNOWS_NO_ALTERNATIVES), asked)
                            .forEach(this::notTaken);
            // Some element, asked nothing of it, is the container holding one: a count, which a path
            // holds.
            case Proposition.Some(DecisionSubject.AnInput(TermPath container),
                                  Proposition.Always(boolean anyElement), boolean holds, var _)
                    when anyElement -> holdingOne(container, holds);
            // Some element meeting something is the container holding one as well, which is taken
            // where a path names the count; which element it is, is not.
            case Proposition.Some(DecisionSubject.AnInput(TermPath container), var _,
                                  boolean holds, var _) when holds -> {
                tookTheCount(container, true);
                WhyNotTaken.declinedWhole(new WhyNotTaken.OutsideDomain(
                        WhyNotTaken.DomainLimit.A_PATH_KNOWS_NO_ALTERNATIVES), asked)
                        .forEach(this::notTaken);
            }
            // Some element is one of several; every element is a fact a path holds only as the
            // closure it was written with.
            case Proposition.Some some -> WhyNotTaken.declinedWhole(new WhyNotTaken.OutsideDomain(
                    some.holds() ? WhyNotTaken.DomainLimit.A_PATH_KNOWS_NO_ALTERNATIVES
                            : WhyNotTaken.DomainLimit.A_PATH_HOLDS_ELEMENT_FACTS_AS_WRITTEN),
                    asked).forEach(this::notTaken);
            // Some node of a search is one of several, and every node of one is what the body
            // states of each, the same way.
            case Proposition.SomeReachable reached -> WhyNotTaken.declinedWhole(
                    new WhyNotTaken.OutsideDomain(reached.holds()
                            ? WhyNotTaken.DomainLimit.A_PATH_KNOWS_NO_ALTERNATIVES
                            : WhyNotTaken.DomainLimit.A_PATH_HOLDS_ELEMENT_FACTS_AS_WRITTEN),
                    asked).forEach(this::notTaken);
            case Proposition.Unread unread ->
                    notTaken(new WhyNotTaken.MeaningUnread(unread.why()));
            case Proposition.Carried carried -> throw carried.handedToAReader();
            case Proposition.Compared(Relation.Ordered ordered, boolean holds, var _) ->
                    onAnOrder(ordered, holds);
            case Proposition.Truth(DecisionSubject.AnAnswer answer, boolean holds, var _) -> {
                Core standing = answering(answer);
                if (standing != null) {
                    known = known.taking(terms.subjectOf(standing, at), holds,
                            Known.Held.ON_THE_PATH);
                    taken = true;
                } else {
                    outside(WhyNotTaken.DomainLimit.A_PLACE_THE_PATH_DOES_NOT_READ);
                }
            }
            case Proposition.Present(DecisionSubject of, boolean holds, var _) ->
                    inCases(of, CasesLeft.of(Refinement.of(new Case.Presence(holds))));
            case Proposition.InCases(DecisionSubject of, CasesLeft cases, boolean holds, var _)
                    when holds -> inCases(of, cases);
            // A value none of some cases is one of the rest of what its type divides into, which
            // is not read here.
            case Proposition.InCases _ ->
                    outside(WhyNotTaken.DomainLimit.A_PATH_KNOWS_NO_CASE_A_VALUE_IS_NOT);
            case Proposition.SameValue _, Proposition.LastToHold _ ->
                    outside(WhyNotTaken.DomainLimit.A_PATH_KNOWS_NO_SAMENESS_OF_VALUES);
        }
    }

    /**
     * A relation's form over what a path knows, or the edges of what it knows that the form meets.
     *
     * <p>Only edges: the statement the form is of was read to the end, so nothing that stops it
     * here is a part of the statement left unread. What stops is what a path can keep a fact in.
     */
    sealed interface FormAt {

        record Named(LinearForm<FactSubject> form) implements FormAt {}

        record Unnamed(Set<WhyNotTaken.DomainLimit> edges) implements FormAt {

            public Unnamed {
                // In the order the edges are declared in, and not the order the form's numbers
                // came in, so what a path says it did not take is the same however it was spelled.
                edges = edges.isEmpty() ? edges
                        : Collections.unmodifiableSet(EnumSet.copyOf(edges));
                if (edges.isEmpty()) {
                    throw new IllegalArgumentException("a form not named meets some edge");
                }
            }
        }
    }

    /** What one number of a statement is on what a path knows: the fact it is, or the edge of what
     *  a path knows it meets. */
    sealed interface AtomAt {

        record Named(FactSubject subject) implements AtomAt {}

        record AtTheEdge(WhyNotTaken.DomainLimit edge) implements AtomAt {}
    }

    /** {@code form} over the atoms this tree names ({@link #formOver}). */
    private FormAt formAt(LinearForm<Quantity> form) {
        return formOver(form, this::atomAt);
    }

    /**
     * {@code form} over what a path knows, each of its numbers named by {@code naming}.
     *
     * <p>Two numbers of the statement named as one fact are one value, and their weights add, all of
     * them at once ({@link LinearForm#sum}); where the exact arithmetic cannot hold what they add
     * to, that is the edge the form meets, since the fact would be kept in a number a path cannot
     * hold. Every edge the form's numbers meet is said, once each, so neither which is said nor
     * whether the weights are held turns on the order the numbers stand in.
     */
    static FormAt formOver(LinearForm<Quantity> form, Function<Quantity, AtomAt> naming) {
        List<LinearForm<FactSubject>> terms = new ArrayList<>();
        terms.add(LinearForm.constant(form.constant()));
        Set<WhyNotTaken.DomainLimit> edges = EnumSet.noneOf(WhyNotTaken.DomainLimit.class);
        for (Map.Entry<Quantity, ExactRatio> each : form.coefs().entrySet()) {
            switch (naming.apply(each.getKey())) {
                case AtomAt.AtTheEdge(var edge) -> edges.add(edge);
                case AtomAt.Named(var subject) ->
                        terms.add(LinearForm.weighing(subject, each.getValue()));
            }
        }
        LinearForm<FactSubject> over = null;
        switch (LinearForm.sum(terms)) {
            case ExactAnswer.Held<LinearForm<FactSubject>> held -> over = held.value();
            case ExactAnswer.Unheld<LinearForm<FactSubject>> _ ->
                    edges.add(WhyNotTaken.DomainLimit.A_NUMBER_THE_PATH_CANNOT_HOLD);
        }
        return edges.isEmpty() ? new FormAt.Named(over) : new FormAt.Unnamed(edges);
    }

    /**
     * What {@code quantity} is on what a path knows here: a count of elements is no fact a path
     * holds, and a place, an answer or a binding this tree has no subject for is a place it does
     * not read.
     */
    private AtomAt atomAt(Quantity quantity) {
        FactSubject named;
        switch (quantity) {
            case DecisionAtom.OfTheInput(NumericTerm term) -> named = atomOf(term);
            case DecisionAtom.OfAnAnswer(DecisionSubject.AnAnswer answer) ->
                    named = answerAtom(answer);
            case Quantity.OfABinding bound -> named = boundAtom(bound);
            case Quantity.HowManyMeet _, Quantity.HowManyHold _ -> {
                return new AtomAt.AtTheEdge(
                        WhyNotTaken.DomainLimit.A_PATH_KNOWS_NO_COUNT_OF_ELEMENTS);
            }
            case Quantity.HowManyDifferent _, Quantity.SumOver _ -> {
                return new AtomAt.AtTheEdge(
                        WhyNotTaken.DomainLimit.A_PATH_KNOWS_NO_NUMBER_OVER_ELEMENTS);
            }
            case Quantity.RemainderOfADividend remainder -> named = remainderOfAForm(remainder);
            // Taken of a form of several places, which is a fact about none of them — or what an
            // operation answered of a place, which a path names only by what it was made of.
            case Quantity.CodePointsOfAPiece _, DecisionAtom.TakenOfAnAnswer _,
                 Quantity.WhatAnOperationAnswers _ -> {
                return new AtomAt.AtTheEdge(
                        WhyNotTaken.DomainLimit.A_PLACE_THE_PATH_DOES_NOT_READ);
            }
        }
        return named != null ? new AtomAt.Named(named)
                : new AtomAt.AtTheEdge(WhyNotTaken.DomainLimit.A_PLACE_THE_PATH_DOES_NOT_READ);
    }

    /**
     * The atom a number of the input is here, or null where it is none this can name: a value at
     * a chain of fields from a parameter, or a size of one.
     *
     * <p>A size carries what its operation bounds its result to, of the value and not of the path:
     * a size is never negative whether or not the condition holds.
     */
    private FactSubject atomOf(NumericTerm term) {
        return switch (term) {
            case NumericTerm.ValueOf(TermPath at) -> {
                Type type = places.typeAt().apply(at);
                yield type == null ? null : terms.atomAt(placeOf(at), type);
            }
            case NumericTerm.TakenOf taken when taken.arguments().equals(TakenArguments.NONE)
                    && isASize(taken) -> {
                FactSubject size = terms.sizeAtPlace(taken.operation(), placeOf(taken.position()));
                if (size != null) {
                    carrying(size, taken.operation());
                }
                yield size;
            }
            // What a division leaves of the value at a place, named as the call that takes it is, so
            // a guard on the remainder here and one on the value a body bound the call to are about
            // one number. It carries both ends its operation bounds it to by this divisor.
            case NumericTerm.TakenOf taken
                    when taken.takenAs() instanceof TakenAs.TheFloorRemainder remainder
                    && remainder.read(taken.arguments()) instanceof BigDecimal divisor
                    && isAWholeNumberOfALong(divisor) -> {
                FactSubject left = terms.remainderAtPlace(taken.operation(),
                        placeOf(taken.position()), divisor.longValue());
                if (left != null) {
                    carryingBothEnds(left, taken.operation(), taken.arguments());
                }
                yield left;
            }
            default -> null;
        };
    }

    /**
     * What a division leaves of a form of places, named by the form's places and the divisor, so a
     * guard on it here and one in the next condition are about one number however each was
     * written; it carries both ends its operation bounds it to by this divisor, the account a
     * remainder of one place carries. Null where a place of the form is none this names.
     *
     * <p>A fact about the remainder and none about its places: a path that knows it holds no more
     * of what the places are than that their form leaves it.
     */
    private FactSubject remainderOfAForm(Quantity.RemainderOfADividend remainder) {
        if (remainder.divisor().bitLength() >= Long.SIZE
                || !(remainder.dividend().constant().floor()
                        instanceof ExactAnswer.Held<BigInteger>(BigInteger constant))) {
            return null;
        }
        List<Map.Entry<FactSubject, BigDecimal>> weighed = new ArrayList<>();
        for (Map.Entry<NumericTerm, ExactRatio> each
                : NumericTerms.entriesInOrder(remainder.dividend().coefs())) {
            FactSubject place = atomOf(each.getKey());
            if (place == null || !(each.getValue().floor()
                    instanceof ExactAnswer.Held<BigInteger>(BigInteger weight))) {
                return null;
            }
            weighed.add(Map.entry(place, new BigDecimal(weight)));
        }
        FactSubject left = terms.remainderOfAForm(remainder.operation(), weighed,
                new BigDecimal(constant), remainder.divisor().longValue());
        if (left != null) {
            carryingBothEnds(left, remainder.operation(), remainder.arguments());
        }
        return left;
    }

    /** Whether {@code number} is a whole number other than nought that a signed 64-bit number holds,
     *  the least one and the greatest included. */
    private static boolean isAWholeNumberOfALong(BigDecimal number) {
        BigInteger whole = Arithmetic.AFloorRemainder.wholeDivisorOf(number);
        return whole != null && whole.bitLength() < Long.SIZE;
    }

    /** {@code atom} held between the ends {@code operation} bounds what it answers to, for the
     *  arguments it was given beside the value. */
    private void carryingBothEnds(FactSubject atom, ValueName operation, TakenArguments given) {
        NumericDomain.Bounds range = ResultRange.of(
                DefaultBoundOperationFacts.get().boundsOnTheResult(operation),
                argument -> Optional.ofNullable(given.at(argument.position())));
        if (range.min() != null) {
            ExactRatio at = Count.number(range.min().at()).exactly();
            known = known.taking(LinearForm.atomMinusConstant(atom, at),
                    range.min().inclusive() ? Rel.GE : Rel.GT, Known.Held.OF_THE_VALUE,
                    terms.kindsOf(LinearForm.atom(atom)));
        }
        if (range.max() != null) {
            ExactRatio at = Count.number(range.max().at()).exactly();
            known = known.taking(LinearForm.atomMinusConstant(atom, at),
                    range.max().inclusive() ? Rel.LE : Rel.LT, Known.Held.OF_THE_VALUE,
                    terms.kindsOf(LinearForm.atom(atom)));
        }
    }

    /**
     * The atom a number a dependency answered is here, or null where the condition this reader
     * stands on reads no such place.
     *
     * <p>The evaluation the walk is at: the call, or the name it was given, as this tree has it
     * ({@link InputPlaces#answering}), named as this reader names any expression's atom. So a fact
     * about the answer taken in one condition is a fact about the same value in the next, however
     * each condition names it.
     */
    private FactSubject answerAtom(DecisionSubject.AnAnswer answer) {
        Core standing = answering(answer);
        return standing == null ? null : terms.atomOf(standing, at);
    }

    /** The expression this tree reads {@code answer} at, or null where the condition reads none. */
    private Core answering(DecisionSubject.AnAnswer answer) {
        return places.answering().get(
                new AnswerPlace(answer.answered().evaluation(), answer.steps()));
    }

    /**
     * The atom a number of a value the body bound is here, by the binding — the value the binding
     * stands for where the condition stands, and the fields read off it — or null where no binding
     * of that name is in force or its number is none the domain carries.
     *
     * <p>Taken in by which value it is, which is all the proposition says of it. What the value was
     * made from is no part of the statement; where the reading of it stopped, a path does not know
     * what the value can be, and an arm left unsettled past it is left there by that and says so.
     */
    private FactSubject boundAtom(Quantity.OfABinding bound) {
        bound.madeOf().ifPresent(why -> notTaken(new WhyNotTaken.MeaningUnread(why)));
        FactSubject value = at.subject(bound.binding());
        RuleKey named = TermPath.ruleKeyOf(bound.steps());
        return value == null || named == null ? null
                : terms.atomAt(terms.under(value, named), bound.type());
    }

    /**
     * A value of the input held against a written place on its order, taken in as the range it
     * leaves the value on the path.
     *
     * <p>Where the value sits on its order and not a number: two strings do not add, so the range
     * is the whole of what such a comparison says and is held where ranges on an order are, beside
     * the values the position admits. A value the comparison says is not the place is a hole and no
     * range, so it is left out with the limit it meets, as is a quantity that is no value of the
     * input.
     */
    private void onAnOrder(Relation.Ordered ordered, boolean holds) {
        TermPath at = ordered.term() instanceof DecisionAtom.OfTheInput(
                NumericTerm.ValueOf(TermPath value)) ? value : null;
        FactSubject place = at == null ? null : placeOf(at);
        Type type = place == null ? null : places.typeAt().apply(at);
        Carrier carrier = type == null ? null : Carrier.ofValue(type, terms.declarations());
        OrderedInterval range = rangeOf(holds ? ordered.proposition()
                : ordered.proposition().denied(), ordered.at());
        if (carrier == null || range == null) {
            outside(WhyNotTaken.DomainLimit.A_PATH_KNOWS_NO_PLACE_ON_AN_ORDER);
            return;
        }
        known = known.bounding(OrderedIntervals.at(place, range), Map.of(place, carrier));
        taken = true;
    }

    /** What {@code rel} against {@code at} leaves a value on the order, or null where it leaves a
     *  hole rather than a range. */
    private static OrderedInterval rangeOf(Rel rel, Place at) {
        return switch (rel) {
            case GE -> new OrderedInterval(Endpoint.inclusive(at), null);
            case GT -> new OrderedInterval(Endpoint.exclusive(at), null);
            case LE -> new OrderedInterval(null, Endpoint.inclusive(at));
            case LT -> new OrderedInterval(null, Endpoint.exclusive(at));
            case EQ -> new OrderedInterval(Endpoint.inclusive(at), Endpoint.inclusive(at));
            case NE -> null;
        };
    }

    /**
     * The value {@code of} is one of {@code cases}, taken in under the subject a fork on it in the
     * tree names it by, so an arm further in on the same value is read under it
     * ({@link Known#inCases}).
     */
    private void inCases(DecisionSubject of, CasesLeft cases) {
        FactSubject value = switch (of) {
            case DecisionSubject.AnInput(TermPath at) -> placeOf(at);
            case DecisionSubject.AnAnswer answer -> {
                Core standing = answering(answer);
                yield standing == null ? null : terms.subjectOf(standing, at);
            }
        };
        if (value == null) {
            outside(WhyNotTaken.DomainLimit.A_PLACE_THE_PATH_DOES_NOT_READ);
            return;
        }
        known = known.inCases(value, cases);
        taken = true;
    }

    /**
     * One of {@code any}'s parts holding, taken as far as a path holds it.
     *
     * <p>Which part holds is no fact of a path, but a part that cannot hold under what is known is
     * one the others are left to: each part is taken alone, from what is known here, and one that
     * leaves nothing is dropped. None left is nothing reached; one left is that one holding, taken
     * as it would be on its own. Two or more left is which of them holds, and is declined.
     *
     * <p>A part taken only in part and still leaving nothing is dropped all the same: what it left
     * out would only have narrowed further.
     *
     * <p>The parts after a second one left are not taken: two left already decline it, whichever
     * the rest come to.
     *
     * <p>And none past the count this reading takes alone ({@link Tries}). A part not taken
     * may be the one that leaves something or the one that leaves nothing, so what the parts
     * taken came to settles nothing — not even none left, which is a proof that no run arrives —
     * and the whole is declined for the count rather than for what a path knows. So is a choice
     * between two left where one of them declined a disjunction for the count: that part may
     * leave nothing, and which of them holds may be no choice at all.
     *
     * <p>Except a choice between comparisons of one whole number, which is no choice for a path to
     * make: it is the runs of the number it leaves ({@link #holdingTheValues}), and those are a
     * fact a path holds however many numbers are in them.
     */
    private void takingOneOf(Proposition.Any any) {
        // Which number the parts compare is asked of the statement before anything is named, so
        // a choice over several numbers costs nothing here, and the one number of a choice over
        // one is named once and not once for each comparison.
        Set<Quantity> numbers = new LinkedHashSet<>();
        if (comparesOnlyNumbers(any, numbers) && numbers.size() == 1
                && isAWholeNumber(numbers.iterator().next())
                && atomAt(numbers.iterator().next()) instanceof AtomAt.Named(FactSubject number)
                && terms.kindsOf(LinearForm.atom(number)).get(number) == Granularity.DISCRETE) {
            WholeNumberRuns values = leftOf(any);
            if (values != null) {
                holdingTheValues(number, values);
                return;
            }
        }
        List<MeaningAssumptions> left = new ArrayList<>();
        for (Proposition part : any.parts()) {
            if (!tries.another()) {
                WhyNotTaken.declinedWhole(new WhyNotTaken.MoreAlternativesThanAreTried(), any)
                        .forEach(this::notTaken);
                return;
            }
            MeaningAssumptions alone = new MeaningAssumptions(terms, places, at, known, tries);
            alone.take(part);
            if (!alone.known.reachesNothing()) {
                left.add(alone);
                if (left.size() == 2) {
                    break;
                }
            }
        }
        switch (left.size()) {
            case 0 -> {
                known = known.reachingNothing();
                taken = true;
            }
            case 1 -> {
                MeaningAssumptions only = left.getFirst();
                known = only.known;
                taken |= only.taken;
                only.notTaken.forEach(this::notTaken);
            }
            default -> {
                boolean cutShort = left.stream().anyMatch(each -> each.notTaken.contains(
                        new WhyNotTaken.MoreAlternativesThanAreTried()));
                WhyNotTaken.declinedWhole(cutShort ? new WhyNotTaken.MoreAlternativesThanAreTried()
                        : new WhyNotTaken.OutsideDomain(
                                WhyNotTaken.DomainLimit.A_PATH_KNOWS_NO_ALTERNATIVES), any)
                        .forEach(this::notTaken);
            }
        }
    }

    /**
     * Whether every part of {@code stated} is a comparison of one number weighed by something other
     * than nought, or settled whatever the numbers are — with each number compared added to
     * {@code numbers}. Asked of the statement alone, so nothing is named.
     */
    private static boolean comparesOnlyNumbers(Proposition stated, Set<Quantity> numbers) {
        return switch (stated) {
            case Proposition.Always _ -> true;
            case Proposition.All all ->
                    all.parts().stream().allMatch(part -> comparesOnlyNumbers(part, numbers));
            case Proposition.Any any ->
                    any.parts().stream().allMatch(part -> comparesOnlyNumbers(part, numbers));
            case Proposition.Compared(Relation.Affine(LinearForm<Quantity> form, Rel _),
                                      boolean _, var _)
                    when form.coefs().size() == 1
                    && form.coefs().values().iterator().next().signum() != 0 -> {
                numbers.add(form.coefs().keySet().iterator().next());
                yield true;
            }
            default -> false;
        };
    }

    /**
     * The whole numbers {@code stated} leaves the one number it compares, which
     * {@link #comparesOnlyNumbers} has said it is over — or null where a threshold is one the exact
     * arithmetic cannot step from.
     *
     * <p>Every part is read, and each exactly: a part this cannot say exactly leaves the whole to be
     * taken some other way, since runs that left out values a part lets through would be a path
     * refusing them.
     */
    private static WholeNumberRuns leftOf(Proposition stated) {
        return switch (stated) {
            case Proposition.Always(boolean holds) ->
                    holds ? WholeNumberRuns.EVERY : WholeNumberRuns.NONE;
            case Proposition.All all -> {
                WholeNumberRuns out = WholeNumberRuns.EVERY;
                for (Proposition part : all.parts()) {
                    WholeNumberRuns each = leftOf(part);
                    if (each == null) {
                        yield null;
                    }
                    out = out.and(each);
                }
                yield out;
            }
            case Proposition.Any any -> {
                WholeNumberRuns out = WholeNumberRuns.NONE;
                for (Proposition part : any.parts()) {
                    WholeNumberRuns each = leftOf(part);
                    if (each == null) {
                        yield null;
                    }
                    out = out.or(each);
                }
                yield out;
            }
            case Proposition.Compared(Relation.Affine(LinearForm<Quantity> form, Rel p),
                                      boolean holds, var _) -> leftBy(form, holds ? p : p.denied());
            default -> throw new IllegalStateException(
                    "a part that compares no number was let through: " + stated);
        };
    }

    /** The whole numbers {@code form rel 0} leaves the one number it is over. */
    private static WholeNumberRuns leftBy(LinearForm<Quantity> form, Rel rel) {
        ExactRatio weight = form.coefs().values().iterator().next();
        if (!(form.constant().negated().dividedBy(weight)
                instanceof ExactAnswer.Held<ExactRatio>(ExactRatio threshold))) {
            return null;
        }
        // Weighed below nought, the number stands the other way round to where the form does.
        return WholeNumberRuns.standing(weight.signum() < 0 ? rel.turned() : rel, threshold);
    }

    /**
     * Whether {@code quantity} is a whole number whose values a path may hold as a set of numbers:
     * a position whose values are counted in ones, or what a size or a division answers of the
     * input, which are such numbers whatever they are taken of.
     *
     * <p>A position counted some other way is left out — a date is counted in days, and the values
     * a path holds of it are dates — and so is anything a path names by what it was made of.
     */
    private boolean isAWholeNumber(Quantity quantity) {
        return switch (quantity) {
            case DecisionAtom.OfTheInput(NumericTerm.ValueOf(TermPath position)) -> {
                Type type = places.typeAt().apply(position);
                yield type != null
                        && Carrier.ofValue(type, terms.declarations()) instanceof Carrier.Whole;
            }
            case DecisionAtom.OfTheInput(NumericTerm.TakenOf taken) ->
                    taken.takenAs() instanceof TakenAs.TheFloorRemainder || isASize(taken);
            case Quantity.RemainderOfADividend _ -> true;
            default -> false;
        };
    }

    /**
     * {@code values} of {@code number}, met with where what is known here leaves it, taken in: as
     * nothing reached where none are left, as the range they are where they are one run, and as
     * the runs of them where they are several ({@link ValueSet#wholeNumbers}).
     *
     * <p>The range on its own where it is one, because the numbers relate the number to others and
     * a set relates it to nothing. Several runs are what the numbers have no word for, and the
     * values beside them are met with where the numbers leave the number, which is where a
     * contradiction between the two is found ({@link ConstraintState#isBottom}).
     *
     * <p>On the path only: a condition says it, and it is no fact of the value wherever the value
     * is named ({@link Known#holdingOnThePath}).
     */
    private void holdingTheValues(FactSubject number, WholeNumberRuns values) {
        WholeNumberRuns held = values.and(rangeOf(number));
        taken = true;
        if (held.isNone()) {
            known = known.reachingNothing();
            return;
        }
        if (held.runs().size() == 1) {
            Map<FactSubject, Granularity> kinds = terms.kindsOf(LinearForm.atom(number));
            WholeNumberRuns.Run run = held.runs().getFirst();
            if (run.from() != null) {
                known = known.taking(LinearForm.atomMinusConstant(number, ExactRatio.of(run.from())),
                        Rel.GE, Known.Held.ON_THE_PATH, kinds);
            }
            if (run.to() != null) {
                known = known.taking(LinearForm.atomMinusConstant(number, ExactRatio.of(run.to())),
                        Rel.LE, Known.Held.ON_THE_PATH, kinds);
            }
            return;
        }
        Allowance<FactSubject> sets = terms.policy().allowanceForAdmittedValues();
        Confinement.Planned<FactSubject> said = new Confinement.Planned<>(
                PlannedValues.at(number, AdmittedPlan.of(ValueSet.wholeNumbers(held))),
                OrderedIntervals.top(), Map.of(number, Carrier.WHOLE));
        known = known.holdingOnThePath(said.resolve(sets), sets);
    }

    /** What is known here of where {@code number} lies, as the whole numbers between its ends. */
    private WholeNumberRuns rangeOf(FactSubject number) {
        return switch (known.numbers().projectionOf(number)) {
            case NumericDomain.Projection.NotSpokenOf _ -> WholeNumberRuns.EVERY;
            case NumericDomain.Projection.NothingIsLeft _ -> WholeNumberRuns.NONE;
            case NumericDomain.Projection.Within(NumericDomain.Bounds bounds) ->
                    WholeNumberRuns.between(bounds.min(), bounds.max());
        };
    }

    /**
     * The container at {@code container} holding at least one element, or none where
     * {@code holds} is false, taken in as what its count is: the same atom a clause or a guard
     * stating the count names.
     */
    private void holdingOne(TermPath container, boolean holds) {
        if (!tookTheCount(container, holds)) {
            outside(WhyNotTaken.DomainLimit.A_PLACE_THE_PATH_DOES_NOT_READ);
        }
    }

    /** The same, saying whether the count was named here at all, and nothing about why not. */
    private boolean tookTheCount(TermPath container, boolean holds) {
        Type type = places.typeAt().apply(container);
        ValueName size = type == null ? null : NumericMeasures.takenOf(type, terms.newtypeInners());
        FactSubject count = size == null ? null : terms.sizeAtPlace(size, placeOf(container));
        if (count == null) {
            return false;
        }
        carrying(count, size);
        known = known.taking(LinearForm.atomMinusConstant(count, ExactRatio.ONE),
                holds ? Rel.GE : Rel.LT, Known.Held.ON_THE_PATH,
                terms.kindsOf(LinearForm.atom(count)));
        taken = true;
        return true;
    }

    /** Whether {@code taken} is the count of what its position holds. */
    private boolean isASize(NumericTerm.TakenOf taken) {
        Type at = places.typeAt().apply(taken.position());
        return at != null && taken.operation().equals(
                NumericMeasures.takenOf(at, terms.newtypeInners()));
    }

    /** {@code atom} holding where {@code operation} bounds what it answers. */
    private void carrying(FactSubject atom, ValueName operation) {
        Endpoint least = ResultRange.of(DefaultBoundOperationFacts.get().boundsOnTheResult(operation),
                ConstantArguments.none()).min();
        if (least == null) {
            return;
        }
        ExactRatio at = Count.number(least.at()).exactly();
        known = known.taking(LinearForm.atomMinusConstant(atom, at),
                least.inclusive() ? Rel.GE : Rel.GT, Known.Held.OF_THE_VALUE,
                terms.kindsOf(LinearForm.atom(atom)));
    }

    /**
     * The place a position is in this tree: a chain of fields from a parameter, or what the
     * expression of the condition that reads it names — or null where neither stands for it.
     */
    private FactSubject placeOf(TermPath position) {
        BindingId parameter = places.parameters().get(position.head());
        RuleKey fields = position.ruleKey();
        if (parameter != null && fields != null) {
            return terms.under(terms.placeSubject(parameter), fields);
        }
        Core reading = places.standing().get(position);
        return reading == null ? null : terms.subjectOf(reading, at);
    }
}
