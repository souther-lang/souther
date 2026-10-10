package souther.compiler.partition;

import souther.compiler.check.NumericMeasures;
import souther.compiler.flow.AWayThrough;
import souther.compiler.flow.WhyRuledOut;
import souther.compiler.inputs.Admits;
import souther.compiler.inputs.Case;
import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.Distinctions;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.Quantities;
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
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Rel;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Whether some input the rules admit brings what a condition states out one way.
 *
 * <p>Asked of the proposition and not of how the condition was written, so two spellings of one
 * condition leave the same ways. A relation over numbers of the input is asked of the run of
 * values the rules leave the number, and a way stands where some value of that run falls on the
 * side the way needs.
 *
 * <p><b>Ruled out is a proof and nothing else is.</b> A way is ruled out only where the rules leave
 * no value behind it. Everything else is not ruled out, and says which parts were not asked of the
 * rules at all, which is a part nothing read. A case, a truth or a value being there is asked of
 * what the rules leave the position; some element meeting something, of what they leave one element
 * and the container's size; and a number that is none of the input's — what a dependency answered,
 * what the body works out — is one the rules range over none of. A conjunction is ruled out where
 * one of its parts is, and a disjunction where every part is — each part asked on its own, which is
 * weaker than asking them together and never wrong the other way. Not ruled out is never a witness
 * that a run takes the way ({@link AWayThrough}).
 */
public final class WhatTheRulesLeave {

    private WhatTheRulesLeave() {}

    private static final AWayThrough LEFT = new AWayThrough.NotRuledOut(List.of());

    /** Whether the rules leave some input on which {@code stated} comes out {@code want}. */
    public static AWayThrough admits(Proposition stated, boolean want, InputReading read) {
        return switch (stated) {
            case Proposition.Always always -> always.holds() == want ? LEFT
                    : new AWayThrough.RuledOut(new WhyRuledOut.ItNeverComesOutSo());
            case Proposition.Compared compared ->
                    leaves(compared.relation(), compared.holds() == want, read.quantities());
            case Proposition.All all -> want ? every(all.parts(), true, read)
                    : some(all.parts(), false, read);
            case Proposition.Any any -> want ? some(any.parts(), true, read)
                    : every(any.parts(), false, read);
            // On some application, either way: each statement is denied where it stands.
            case Proposition.OnAnApplication applications ->
                    some(applications.each(), want, read);
            case Proposition.Unread unread ->
                    notAsked(new WhyNotTaken.MeaningUnread(unread.why()));
            // What a dependency answered is what a row stands it in with, and the input's rules
            // say nothing of that.
            case Proposition.Truth(DecisionSubject.AnAnswer _, boolean _, var _),
                 Proposition.InCases(DecisionSubject.AnAnswer _, var _, boolean _, var _),
                 Proposition.Present(DecisionSubject.AnAnswer _, boolean _, var _) -> LEFT;
            case Proposition.Truth(DecisionSubject.AnInput(TermPath at), boolean holds, var _) ->
                    leaves(at, List.of(new Case.Truth(holds == want)), read);
            case Proposition.Present(DecisionSubject.AnInput(TermPath at), boolean holds,
                                     var _) ->
                    leaves(at, List.of(new Case.Presence(holds == want)), read);
            case Proposition.InCases(DecisionSubject.AnInput(TermPath at), CasesLeft cases,
                                     boolean holds, var _) ->
                    amongCases(at, cases, holds == want, read);
            // Whether two values are one is no rule of either position alone, so asked of each
            // on its own, nothing rules it out.
            case Proposition.SameValue _ -> LEFT;
            case Proposition.Some some -> someElement(some, some.holds() == want, read);
        };
    }

    /**
     * Whether the rules leave the value at {@code at} one of {@code cases} — ruled out only where
     * they refuse every one of them, and not ruled out where they leave one or were not read far
     * enough to say.
     */
    private static AWayThrough leaves(TermPath at, List<Case> cases, InputReading read) {
        Position position = read.domain().at(at.position());
        if (position == null) {
            return LEFT;
        }
        for (Case each : cases) {
            if (!(position.admissionOf(each) instanceof Admits.Refused)) {
                return LEFT;
            }
        }
        return new AWayThrough.RuledOut(new WhyRuledOut.TheRulesRefuseEveryCase(at, cases));
    }

    /**
     * Whether the value at {@code at} is left one of {@code cases} where {@code among}, or none of
     * them where not.
     *
     * <p>Asked of the cases its type divides into that are the way asked, and of the rules about
     * each. Where none of them is, the answer turns on why. A declaration that lists every case of
     * its sum in the vocabulary the statement names cases in has said the value is always one of
     * those, so none being the way asked rules the way out. A declaration that lists none — a
     * record, a collection, a type this reading has nothing to say about — or lists them in another
     * vocabulary has not said that: an empty list is then this reading finding nothing stated
     * ({@link Distinctions}), and is no proof of anything.
     */
    private static AWayThrough amongCases(TermPath at, CasesLeft cases, boolean among,
                                          InputReading read) {
        Position position = read.domain().at(at.position());
        if (position == null) {
            return LEFT;
        }
        List<Case> declared = Distinctions.ofType(position.view().shape(), read.rules().symbols(),
                read.rules().kinds(), read.rules().sums());
        List<Case> asked = new ArrayList<>();
        for (Case each : declared) {
            Refinement one = Refinement.of(each);
            if (one != null && cases.atoms().contains(one) == among) {
                asked.add(each);
            }
        }
        if (!asked.isEmpty()) {
            return leaves(at, asked, read);
        }
        List<TypeSymbol> leaves = leavesOf(declared);
        List<TypeSymbol> named = namedIn(cases);
        return leaves.isEmpty() || named.isEmpty() ? LEFT
                : new AWayThrough.RuledOut(
                        new WhyRuledOut.TheDeclarationLeavesNone(at, leaves, named, among));
    }

    /** The leaves {@code declared} lists, or none unless it lists nothing but cases of a sum. */
    private static List<TypeSymbol> leavesOf(List<Case> declared) {
        List<TypeSymbol> out = new ArrayList<>();
        for (Case each : declared) {
            if (!(each instanceof Case.SumCase sum)) {
                return List.of();
            }
            out.add(sum.leaf());
        }
        return out;
    }

    /** The leaves {@code cases} names, or none unless it names nothing but cases of a sum. */
    private static List<TypeSymbol> namedIn(CasesLeft cases) {
        List<TypeSymbol> out = new ArrayList<>();
        for (Refinement each : cases.atoms()) {
            if (!(each instanceof Refinement.SumCase sum)) {
                return List.of();
            }
            out.add(sum.leaf());
        }
        return out;
    }

    /**
     * Whether the rules leave some element of the container meeting what is asked of it — or, the
     * other way round, every element meeting its denial: ruled out where they leave no element any
     * value meeting it and, for every element, the container no way of holding none.
     *
     * <p>The element asked of on its own, as every element is: what the rules leave one element is
     * what they leave each, and which element it is is no rule's.
     */
    private static AWayThrough someElement(Proposition.Some some, boolean someMeets,
                                           InputReading read) {
        AWayThrough element = admits(some.ofTheElement(), someMeets, read);
        if (someMeets) {
            return element instanceof AWayThrough.RuledOut || mayHold(some.container(), true, read)
                    ? element : new AWayThrough.RuledOut(
                            new WhyRuledOut.NothingIsHeldIn(some.container()));
        }
        return mayHold(some.container(), false, read) ? LEFT : element;
    }

    /**
     * Whether the rules leave the container at {@code at} holding at least one, or none, as its
     * size: where no size of it is a number of the input they leave it either.
     */
    private static boolean mayHold(TermPath at, boolean atLeastOne, InputReading read) {
        Type container = read.domain().typeAt(at, read.rules());
        ValueName.Stdlib size = container == null ? null
                : NumericMeasures.takenOf(container, read.rules().inners());
        NumericTerm.TakenOf count = size == null ? null : NumericTerm.TakenOf.of(size, at,
                container, read.rules().inners(), read.rules().symbols());
        return count == null || someValue(read.quantities().runsBetween(count),
                atLeastOne ? Rel.GE : Rel.LE, atLeastOne ? Count.of(1) : Count.ZERO);
    }

    /** Every one of {@code parts} coming out {@code want}: ruled out where one of them is. */
    private static AWayThrough every(List<Proposition> parts, boolean want, InputReading read) {
        List<WhyNotTaken> notAsked = new ArrayList<>();
        for (Proposition part : parts) {
            switch (admits(part, want, read)) {
                case AWayThrough.RuledOut out -> {
                    return out;
                }
                case AWayThrough.NotRuledOut(List<WhyNotTaken> whys) -> notAsked.addAll(whys);
            }
        }
        return left(notAsked);
    }

    /** Not ruled out, with what was not asked: the one answer where nothing was left unasked. */
    private static AWayThrough left(List<WhyNotTaken> notAsked) {
        return notAsked.isEmpty() ? LEFT : new AWayThrough.NotRuledOut(notAsked);
    }

    /** Some one of {@code parts} coming out {@code want}: ruled out where every one is. */
    private static AWayThrough some(List<Proposition> parts, boolean want, InputReading read) {
        List<WhyNotTaken> notAsked = new ArrayList<>();
        List<WhyRuledOut> eachRuledOut = new ArrayList<>();
        boolean somePartLeft = false;
        for (Proposition part : parts) {
            switch (admits(part, want, read)) {
                case AWayThrough.NotRuledOut(var whys) -> {
                    somePartLeft = true;
                    notAsked.addAll(whys);
                }
                case AWayThrough.RuledOut(var why) -> eachRuledOut.add(why);
            }
        }
        if (somePartLeft) {
            return left(notAsked);
        }
        // Ruled out by every part, so the reason is all of theirs. A statement of no parts leaves
        // no way to come out so, which is what the empty disjunction states.
        return new AWayThrough.RuledOut(eachRuledOut.isEmpty()
                ? new WhyRuledOut.ItNeverComesOutSo()
                : eachRuledOut.size() == 1 ? eachRuledOut.get(0)
                : new WhyRuledOut.EveryWay(eachRuledOut));
    }

    private static AWayThrough notAsked(WhyNotTaken why) {
        return new AWayThrough.NotRuledOut(List.of(why));
    }

    /**
     * Whether the rules leave a value at which {@code relation} holds, or fails where
     * {@code holds} is false.
     *
     * <p>Over a number that is no number of the input — what a dependency answered, a value the
     * body works out, how many elements meet something — the input's rules range over none of it,
     * so they rule nothing out.
     */
    private static AWayThrough leaves(Relation relation, boolean holds, Quantities rules) {
        Rel asked = holds ? relation.proposition() : relation.proposition().denied();
        return switch (relation) {
            case Relation.Ordered(DecisionAtom.OfTheInput(NumericTerm term), var at, Rel _) ->
                    someValue(rules.runsBetween(term), asked, at) ? LEFT
                            : new AWayThrough.RuledOut(
                                    new WhyRuledOut.TheNumbersLeaveNone(relation, asked));
            case Relation.Ordered _ -> LEFT;
            case Relation.Affine affine -> {
                LinearForm<NumericTerm> form = ofTheInput(affine.form());
                if (form == null) {
                    yield LEFT;
                }
                yield someValue(rules.runsBetween(form), asked, Count.ZERO) ? LEFT
                        : new AWayThrough.RuledOut(
                                new WhyRuledOut.TheNumbersLeaveNone(relation, asked));
            }
        };
    }

    /** {@code form} as one over numbers of the input, or null where a quantity is something else.
     *  The one place a statement's form is put on the input space, for every reader that does. */
    static LinearForm<NumericTerm> ofTheInput(LinearForm<Quantity> form) {
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        for (Map.Entry<Quantity, ExactRatio> each : form.coefs().entrySet()) {
            if (!(each.getKey() instanceof DecisionAtom.OfTheInput(NumericTerm term))) {
                return null;
            }
            coefs.put(term, each.getValue());
        }
        return new LinearForm<>(form.constant(), coefs);
    }

    /** Whether {@code runs} holds a value {@code v} with {@code v asked at}. */
    private static boolean someValue(NumericDomain.Bounds runs, Rel asked, Place at) {
        return switch (asked) {
            case GT -> anythingBeyond(runs, at, true, false);
            case GE -> anythingBeyond(runs, at, true, true);
            case LT -> anythingBeyond(runs, at, false, false);
            case LE -> anythingBeyond(runs, at, false, true);
            case EQ -> anythingBeyond(runs, at, true, true) && anythingBeyond(runs, at, false, true);
            case NE -> anythingBeyond(runs, at, true, false) || anythingBeyond(runs, at, false, false);
        };
    }

    /**
     * Whether the run holds a value on the {@code up} side of {@code at}, taking {@code at} itself
     * where the side {@code inclusive} reaches it.
     *
     * <p>Only the end the side runs towards can close it: everything above a line is still above it
     * however far the run's low end is raised, so a side that reaches past the far end is a side
     * with a value on it.
     *
     * <p>Where the end falls exactly on the line, what is beyond it is the line itself and nothing
     * else, so a side that takes the line has a value there where the run does, and a side that does
     * not has none. That is the one place this closes a way on the run's word: strictly past an end
     * the run stops at, no value stands. Everywhere short of the end this answers that a value
     * stands, whether the run steps or fills there, because that much the end says on its own.
     */
    public static boolean anythingBeyond(NumericDomain.Bounds runs, Place at, boolean up,
                                         boolean inclusive) {
        Endpoint end = runs == null ? null : (up ? runs.max() : runs.min());
        if (end == null || end.at() == null) {
            return true;
        }
        int against = end.at().compareTo(at);
        if (up ? against > 0 : against < 0) {
            return true;
        }
        return against == 0 && inclusive && end.inclusive();
    }
}
