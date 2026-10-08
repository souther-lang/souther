package souther.compiler.check;

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
import java.util.HashMap;
import java.util.List;
import java.util.Map;
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
 * meets something, since which element is not known; a case, a value being present, a relation on
 * an order, and a part nothing read. Each is left out, which is the sound answer with less: a path
 * that took nothing in has ruled nothing out.
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
     */
    record InputPlaces(Map<String, BindingId> parameters, Function<TermPath, Type> typeAt,
                       Map<TermPath, Core> standing) {

        /** Where nothing stands: no proposition names a place here. */
        static final InputPlaces NONE = new InputPlaces(Map.of(), path -> null, Map.of());

        InputPlaces {
            standing = Map.copyOf(standing);
        }

        /** The same places, with what a condition reads standing at each position it reads. */
        InputPlaces readBy(Map<TermPath, Core> condition) {
            return new InputPlaces(parameters, typeAt, condition);
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

    private void incomplete(WhyNotTaken.Shape shape) {
        notTaken(new WhyNotTaken.ProjectionIncomplete(shape));
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
                LinearForm<FactSubject> over = formAt(form);
                if (over != null) {
                    known = known.taking(over, holds ? p : p.denied(), Known.Held.ON_THE_PATH,
                            terms.kindsOf(over));
                    taken = true;
                } else if (form.coefs().keySet().stream().anyMatch(atom ->
                        atom instanceof DecisionAtom.OfAnAnswer
                                || atom instanceof Quantity.HowManyMeet)) {
                    WhyNotTaken.quantitiesNoRowWrites(form).forEach(this::notTaken);
                } else {
                    incomplete(WhyNotTaken.Shape.A_POSITION_THE_PATH_HAS_NO_PLACE_FOR);
                }
            }
            case Proposition.Truth(DecisionSubject.AnInput(TermPath at), boolean holds, var _) -> {
                FactSubject place = placeOf(at);
                if (place != null) {
                    known = known.taking(place, holds, Known.Held.ON_THE_PATH);
                    taken = true;
                } else {
                    incomplete(WhyNotTaken.Shape.A_POSITION_THE_PATH_HAS_NO_PLACE_FOR);
                }
            }
            case Proposition.Always _ -> { }
            // What a path knows is facts that all hold, and which of several holds, or which
            // element, is no fact of it.
            case Proposition.Any _, Proposition.OnAnApplication _, Proposition.Some _ ->
                    WhyNotTaken.declinedWhole(new WhyNotTaken.OutsideDomain(
                            WhyNotTaken.DomainLimit.A_PATH_KNOWS_NO_ALTERNATIVES), asked)
                            .forEach(this::notTaken);
            case Proposition.Unread unread ->
                    notTaken(new WhyNotTaken.MeaningUnread(unread.why()));
            case Proposition.Compared(Relation.Ordered _, boolean _, var _) ->
                    incomplete(WhyNotTaken.Shape.A_PLACE_ON_AN_ORDER);
            case Proposition.Truth(DecisionSubject.AnAnswer _, boolean _, var _),
                 Proposition.InCases(DecisionSubject.AnAnswer _, var _, boolean _, var _),
                 Proposition.Present(DecisionSubject.AnAnswer _, boolean _, var _) ->
                    incomplete(WhyNotTaken.Shape.WHAT_A_DEPENDENCY_ANSWERED);
            case Proposition.InCases _ -> incomplete(WhyNotTaken.Shape.THE_CASE_OF_A_SUBJECT);
            case Proposition.Present _ -> incomplete(WhyNotTaken.Shape.A_VALUE_BEING_THERE);
            case Proposition.SameValue _ -> incomplete(WhyNotTaken.Shape.TWO_SUBJECTS_ONE_VALUE);
        }
    }

    /** {@code form} over the atoms this tree names, or null where one of them it cannot name. */
    private LinearForm<FactSubject> formAt(LinearForm<Quantity> form) {
        Map<FactSubject, ExactRatio> coefs = new HashMap<>();
        for (Map.Entry<Quantity, ExactRatio> each : form.coefs().entrySet()) {
            FactSubject atom = switch (each.getKey()) {
                case DecisionAtom.OfTheInput(NumericTerm term) -> atomOf(term);
                case Quantity.OfABinding bound -> boundAtom(bound);
                // Not asked: what no row writes was said before a form was made of it.
                case DecisionAtom.OfAnAnswer _, Quantity.HowManyMeet _ -> null;
            };
            if (atom == null || coefs.putIfAbsent(atom, each.getValue()) != null) {
                return null;
            }
        }
        return new LinearForm<>(form.constant(), coefs);
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
     * The atom a number of a value the body bound is here, by the binding — the value the binding
     * stands for where the condition stands, and the fields read off it — or null where no binding
     * of that name is in force or its number is none the domain carries.
     */
    private FactSubject boundAtom(Quantity.OfABinding bound) {
        FactSubject value = at.subject(bound.binding());
        // Taken in by which value it is, and not read to the end: what the value was made from is
        // not what the proposition says, so an arm this leaves unsettled is left by this reader's
        // reach and says so.
        incomplete(WhyNotTaken.Shape.A_NUMBER_THE_BODY_BOUND);
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
