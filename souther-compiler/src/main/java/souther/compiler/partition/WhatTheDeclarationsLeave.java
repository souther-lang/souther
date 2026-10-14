package souther.compiler.partition;

import souther.compiler.check.NumericMeasures;
import souther.compiler.flow.AWayThrough;
import souther.compiler.flow.WhyRuledOut;
import souther.compiler.inputs.Admits;
import souther.compiler.inputs.Case;
import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.DeclaredInput;
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
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

/**
 * Whether some input the declarations admit brings what a condition states out one way.
 *
 * <p>The declarations are the types and every rule written on them, read together: a
 * {@code Set<Bool>} holding three values is refused by its element having two, with no rule
 * written, as surely as a value outside an invariant's bound is. Which of them refused a way is
 * not said here, and the word is not "the rules", which an author reads as what they wrote.
 *
 * <p>Asked of the proposition and not of how the condition was written, so two spellings of one
 * condition leave the same ways. A relation over numbers of the input is asked of the run of
 * values the declarations leave the number, and a way stands where some value of that run falls on
 * the side the way needs.
 *
 * <p><b>Ruled out is a proof and nothing else is.</b> A way is ruled out only where the
 * declarations leave no value behind it; what is left is wider than what they admit wherever a
 * part was asked on its own, so it is never read as the values the model admits. Everything else is
 * not ruled out, and says which parts were not asked of the declarations at all, which is a part
 * nothing read. A case, a truth or a value being there is asked of what the declarations leave the
 * position; some element meeting something, of what they leave one element and the container's
 * size; and a number that is none of the input's — what a dependency answered, what the body works
 * out — is one they range over none of. A conjunction is ruled out where one of its parts is, and a
 * disjunction where every part is — each part asked on its own, which is weaker than asking them
 * together and never wrong the other way. Not ruled out is never a witness that a run takes the way
 * ({@link AWayThrough}).
 */
public final class WhatTheDeclarationsLeave {

    private WhatTheDeclarationsLeave() {}

    private static final AWayThrough LEFT = new AWayThrough.NotRuledOut(List.of());

    /**
     * What this reading has already answered, by the statement and the way asked.
     *
     * <p>Kept with the reading because the answer is a function of it and the question is asked
     * many times: every arm of a {@code match} states the denial of the arms before it, so one
     * part is asked once per arm after it, and the readers of a way through and of the branch count
     * ask the same arm of the same reading. Not held across a recursive ask, so a part answered
     * while its whole is being answered is filed on its own.
     */
    private static final class Answered {

        private record Asked(Proposition stated, boolean want) {}

        private final Map<Asked, AWayThrough> filed = new ConcurrentHashMap<>();
    }

    /**
     * Whether the declarations prove that no input brings {@code stated} out {@code want}.
     *
     * <p>{@link AWayThrough.RuledOut} is that proof. {@link AWayThrough.NotRuledOut} is no proof
     * either way — a part nothing read is not ruled out, and neither is one the declarations do
     * leave a value for — so it is never read as some input taking the way.
     */
    public static AWayThrough whetherRuledOut(Proposition stated, boolean want,
                                              InputReading read) {
        // A statement no part of which is about the input is answered without one, and has nothing
        // to be kept with.
        if (read == null) {
            return answer(stated, want, null);
        }
        Answered answered = read.derived(Answered.class, _ -> new Answered());
        Answered.Asked asked = new Answered.Asked(stated, want);
        AWayThrough kept = answered.filed.get(asked);
        if (kept == null) {
            kept = answer(stated, want, read);
            answered.filed.put(asked, kept);
        }
        return kept;
    }

    private static AWayThrough answer(Proposition stated, boolean want, InputReading read) {
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
            case Proposition.Carried carried -> throw carried.handedToAReader();
            // What a dependency answered is what a row stands it in with, and the input's
            // declarations say nothing of that.
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
            case Proposition.SameValue _, Proposition.LastToHold _ -> LEFT;
            // The elements of what a dependency answered are what a row stands it in with, the
            // same as the answer itself.
            case Proposition.Some some when some.container() instanceof DecisionSubject.AnAnswer ->
                    LEFT;
            case Proposition.Some some -> someElement(some, some.holds() == want, read);
            // The declarations are of what a row writes, and a search goes on below as deep as a
            // value does: a node it reaches may meet what the one at the top cannot.
            case Proposition.SomeReachable _ -> LEFT;
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
     * <p>Two facts, asked in this order, and kept apart because they are about different things.
     * What the declaration lets a value there be ({@link DeclaredInput#leavesAt}) is what the type
     * says, whatever the rules are: an arm for a case the type does not hold is ruled out, and an
     * arm for every case the type holds leaves nothing for a denial of it. Only what the type
     * leaves is then asked of the rules about the position, a case at a time
     * ({@link Distinctions}).
     *
     * <p>The declaration's answer is read as every name the value may wear says it, so a position
     * where it is not settled how many names a statement took off is ruled out only where each
     * reading rules it out. Where the declaration says nothing this can follow, the way is not ruled
     * out.
     */
    private static AWayThrough amongCases(TermPath at, CasesLeft cases, boolean among,
                                          InputReading read) {
        List<TypeSymbol> named = namedIn(cases);
        Set<TypeSymbol> anyOf = Set.copyOf(named);
        Optional<List<List<TypeSymbol>>> readings = read.declared().leavesAt(at);
        if (readings.isPresent() && !named.isEmpty() && readings.get().stream().allMatch(
                leaves -> among ? leaves.stream().noneMatch(anyOf::contains)
                        : anyOf.containsAll(leaves))) {
            return new AWayThrough.RuledOut(new WhyRuledOut.TheDeclarationLeavesNone(at,
                    readings.get().getLast(), named, among));
        }
        Position position = read.domain().at(at.position());
        if (position == null) {
            return LEFT;
        }
        List<Case> asked = new ArrayList<>();
        Set<Refinement> atoms = Set.copyOf(cases.atoms());
        for (Case each : Distinctions.ofType(position.view().shape(), read.rules().symbols(),
                read.rules().kinds(), read.rules().sums())) {
            Refinement one = Refinement.of(each);
            if (one != null && atoms.contains(one) == among) {
                asked.add(each);
            }
        }
        return asked.isEmpty() ? LEFT : leaves(at, asked, read);
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
     * Whether the declarations prove no element of the container meets what is asked of it — or,
     * the other way round, that not every element meets its denial: ruled out where they leave no
     * element any value meeting it and, for every element, the container no way of holding none.
     *
     * <p>The element asked of on its own, as every element is: what the declarations leave one
     * element is what they leave each, and which element it is is no rule's.
     */
    private static AWayThrough someElement(Proposition.Some some, boolean someMeets,
                                           InputReading read) {
        AWayThrough element = whetherRuledOut(some.ofTheElement(), someMeets, read);
        if (someMeets) {
            TermPath container = some.container().inputPosition();
            return element instanceof AWayThrough.RuledOut || !provedToHold(container, false, read)
                    ? element : new AWayThrough.RuledOut(
                            new WhyRuledOut.NothingIsHeldIn(container));
        }
        return provedToHold(some.container().inputPosition(), true, read) ? element : LEFT;
    }

    /**
     * Whether the declarations prove the container at {@code at} holds at least one, or holds none,
     * as its size. Where no size of it is a number of the input nothing is proved either way.
     */
    private static boolean provedToHold(TermPath at, boolean atLeastOne, InputReading read) {
        Type container = read.domain().typeAt(at, read.rules());
        ValueName.Stdlib size = container == null ? null
                : NumericMeasures.takenOf(container, read.rules().inners());
        NumericTerm.TakenOf count = size == null ? null : NumericTerm.TakenOf.asItStands(size, at,
                container, read.rules().inners(), read.rules().symbols());
        return count != null && ruledOutByBounds(read.quantities().runsBetween(count),
                atLeastOne ? Rel.LT : Rel.GT, atLeastOne ? Count.of(1) : Count.ZERO);
    }

    /** Every one of {@code parts} coming out {@code want}: ruled out where one of them is. */
    private static AWayThrough every(List<Proposition> parts, boolean want, InputReading read) {
        List<WhyNotTaken> notAsked = new ArrayList<>();
        for (Proposition part : parts) {
            switch (whetherRuledOut(part, want, read)) {
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
            switch (whetherRuledOut(part, want, read)) {
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
     * Whether the declarations prove no value is one at which {@code relation} holds, or fails
     * where {@code holds} is false.
     *
     * <p>Over a number that is no number of the input — what a dependency answered, a value the
     * body works out, how many elements meet something — the input's declarations range over none
     * of it, so they rule nothing out.
     */
    private static AWayThrough leaves(Relation relation, boolean holds, Quantities declared) {
        Rel asked = holds ? relation.proposition() : relation.proposition().denied();
        return switch (relation) {
            case Relation.Ordered(DecisionAtom.OfTheInput(NumericTerm term), var at, Rel _) ->
                    ruledOutByBounds(declared.runsBetween(term), asked, at)
                            ? new AWayThrough.RuledOut(
                                    new WhyRuledOut.TheNumbersLeaveNone(relation, asked))
                            : LEFT;
            case Relation.Ordered _ -> LEFT;
            case Relation.Affine affine -> {
                LinearForm<NumericTerm> form = ofTheInput(affine.form());
                if (form == null) {
                    yield LEFT;
                }
                yield ruledOutByBounds(declared.runsBetween(form), asked, Count.ZERO)
                        ? new AWayThrough.RuledOut(
                                new WhyRuledOut.TheNumbersLeaveNone(relation, asked))
                        : LEFT;
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

    /**
     * Whether {@code runs} proves that no value {@code v} has {@code v asked at}.
     *
     * <p>The one table of what a run's ends rule out, for every reader that asks it. False is no
     * proof having been had, and never that such a value stands: a run with no end on the side, or
     * none read at all, proves nothing either way.
     */
    public static boolean ruledOutByBounds(NumericDomain.Bounds runs, Rel asked, Place at) {
        return switch (asked) {
            case GT -> provesNoValueBeyond(runs, at, true, false);
            case GE -> provesNoValueBeyond(runs, at, true, true);
            case LT -> provesNoValueBeyond(runs, at, false, false);
            case LE -> provesNoValueBeyond(runs, at, false, true);
            // One value, which either side being empty of it leaves out.
            case EQ -> provesNoValueBeyond(runs, at, true, true)
                    || provesNoValueBeyond(runs, at, false, true);
            // Every value but one, so it takes both sides being empty.
            case NE -> provesNoValueBeyond(runs, at, true, false)
                    && provesNoValueBeyond(runs, at, false, false);
        };
    }

    /**
     * Whether {@code runs} proves no value stands on the {@code above} side of {@code at}, taking
     * {@code at} itself where {@code inclusive}.
     *
     * <p>False means no such proof was had, not that a value stands there.
     *
     * <p>Only the end the side runs towards can prove it: everything above a line is still above it
     * however far the run's low end is raised, so a side reaching past the far end is not shown
     * empty, and neither is a side with no end at all.
     *
     * <p>Where the end falls exactly on the line, what is beyond it is the line itself and nothing
     * else, so a side that takes the line is shown empty only where the run's end leaves the line
     * out, and a side that does not take it is shown empty. That is the one place this closes a way
     * on the run's word: strictly past an end the run stops at, no value stands.
     */
    private static boolean provesNoValueBeyond(NumericDomain.Bounds runs, Place at, boolean above,
                                               boolean inclusive) {
        Endpoint end = runs == null ? null : (above ? runs.max() : runs.min());
        if (end == null || end.at() == null) {
            return false;
        }
        int against = end.at().compareTo(at);
        if (above ? against > 0 : against < 0) {
            return false;
        }
        return !(against == 0 && inclusive && end.inclusive());
    }
}
