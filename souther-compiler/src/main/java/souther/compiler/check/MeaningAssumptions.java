package souther.compiler.check;

import souther.compiler.inputs.AnEvaluation;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.core.Core;
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
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.ConstantArguments;
import souther.compiler.semantics.ResultRange;
import souther.compiler.semantics.TakenArguments;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.Collections;
import java.util.EnumSet;
import java.util.List;
import java.util.Map;
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
 * of a container at one — as the relation it states. A truth at a position. Both halves of a
 * conjunction, since both hold. Nothing at all where the condition is never met, since nothing
 * reaches there.
 *
 * <p><b>What is not.</b> A disjunction, since which half holds is not known; that some element
 * meets something, since which element is not known; what every element meets, which a path holds
 * only as the closure it was written with; a case, a value being present, two values being one,
 * a place on an order, a count of elements, a place this tree does not read, and a part nothing
 * read. Each is left out with the limit of {@link Known} it meets, which is the sound answer with
 * less: a path that took nothing in has ruled nothing out.
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

    private MeaningAssumptions(Terms terms, InputPlaces places, Denotations at, Known known) {
        this.terms = terms;
        this.places = places;
        this.at = at;
        this.known = known;
    }

    /** What {@code k} comes to once what {@code stated} states comes out {@code positive}, read
     *  where the bindings {@code at} holds are in force. */
    static Predicates.Assumed assumed(Proposition stated, boolean positive, Known k, Terms terms,
                                      InputPlaces places, Denotations at) {
        Proposition asked = positive ? stated : stated.denied();
        MeaningAssumptions taking = new MeaningAssumptions(terms, places, at, k);
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
            // What a path knows is facts that all hold, and which of several holds, or which
            // element, is no fact of it.
            case Proposition.Any _, Proposition.OnAnApplication _ ->
                    WhyNotTaken.declinedWhole(new WhyNotTaken.OutsideDomain(
                            WhyNotTaken.DomainLimit.A_PATH_KNOWS_NO_ALTERNATIVES), asked)
                            .forEach(this::notTaken);
            // Some element is one of several; every element is a fact a path holds only as the
            // closure it was written with.
            case Proposition.Some some -> WhyNotTaken.declinedWhole(new WhyNotTaken.OutsideDomain(
                    some.holds() ? WhyNotTaken.DomainLimit.A_PATH_KNOWS_NO_ALTERNATIVES
                            : WhyNotTaken.DomainLimit.A_PATH_HOLDS_ELEMENT_FACTS_AS_WRITTEN),
                    asked).forEach(this::notTaken);
            case Proposition.Unread unread ->
                    notTaken(new WhyNotTaken.MeaningUnread(unread.why()));
            case Proposition.Compared(Relation.Ordered _, boolean _, var _) ->
                    outside(WhyNotTaken.DomainLimit.A_PATH_KNOWS_NO_PLACE_ON_AN_ORDER);
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
            case Proposition.InCases _, Proposition.Present _ ->
                    outside(WhyNotTaken.DomainLimit.A_PATH_KNOWS_NO_CASES);
            case Proposition.SameValue _ ->
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
            default -> null;
        };
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
