package souther.compiler.partition;

import souther.compiler.flow.AWayThrough;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Quantities;
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
 * rules at all: a part nothing read, a quantity of something other than the input, a statement
 * about which case a value is, an element of a container. A conjunction is ruled out where one of
 * its parts is, and a disjunction where every part is — each part asked on its own, which is weaker
 * than asking them together and never wrong the other way. Not ruled out is never a witness that a
 * run takes the way ({@link AWayThrough}).
 */
public final class WhatTheRulesLeave {

    private WhatTheRulesLeave() {}

    private static final AWayThrough LEFT = new AWayThrough.NotRuledOut(List.of());

    /** Whether the rules leave some input on which {@code stated} comes out {@code want}. */
    public static AWayThrough admits(Proposition stated, boolean want, Quantities rules) {
        return switch (stated) {
            case Proposition.Always always -> always.holds() == want ? LEFT
                    : new AWayThrough.RuledOut();
            case Proposition.Compared compared ->
                    leaves(compared.relation(), compared.holds() == want, rules);
            case Proposition.All all -> want ? every(all.parts(), true, rules)
                    : some(all.parts(), false, rules);
            case Proposition.Any any -> want ? some(any.parts(), true, rules)
                    : every(any.parts(), false, rules);
            // On some application, either way: each statement is denied where it stands.
            case Proposition.OnAnApplication applications ->
                    some(applications.each(), want, rules);
            case Proposition.Unread unread ->
                    notAsked(new WhyNotTaken.MeaningUnread(unread.why()));
            case Proposition.Truth(DecisionSubject.AnAnswer _, boolean _, var _),
                 Proposition.InCases(DecisionSubject.AnAnswer _, var _, boolean _, var _),
                 Proposition.Present(DecisionSubject.AnAnswer _, boolean _, var _) ->
                    incomplete(WhyNotTaken.Shape.WHAT_A_DEPENDENCY_ANSWERED);
            case Proposition.Truth _ -> incomplete(WhyNotTaken.Shape.A_TRUTH_ASKED_OF_THE_RULES);
            case Proposition.InCases _ -> incomplete(WhyNotTaken.Shape.THE_CASE_OF_A_SUBJECT);
            case Proposition.Present _ -> incomplete(WhyNotTaken.Shape.A_VALUE_BEING_THERE);
            case Proposition.SameValue _ -> incomplete(WhyNotTaken.Shape.TWO_SUBJECTS_ONE_VALUE);
            case Proposition.Some _ -> incomplete(WhyNotTaken.Shape.SOME_ELEMENT_ASKED_OF_THE_RULES);
        };
    }

    /** Every one of {@code parts} coming out {@code want}: ruled out where one of them is. */
    private static AWayThrough every(List<Proposition> parts, boolean want, Quantities rules) {
        List<WhyNotTaken> notAsked = new ArrayList<>();
        for (Proposition part : parts) {
            switch (admits(part, want, rules)) {
                case AWayThrough.RuledOut out -> {
                    return out;
                }
                case AWayThrough.NotRuledOut(List<WhyNotTaken> whys) -> notAsked.addAll(whys);
            }
        }
        return new AWayThrough.NotRuledOut(notAsked);
    }

    /** Some one of {@code parts} coming out {@code want}: ruled out where every one is. */
    private static AWayThrough some(List<Proposition> parts, boolean want, Quantities rules) {
        List<WhyNotTaken> notAsked = new ArrayList<>();
        boolean left = false;
        for (Proposition part : parts) {
            if (admits(part, want, rules) instanceof AWayThrough.NotRuledOut(var whys)) {
                left = true;
                notAsked.addAll(whys);
            }
        }
        return left ? new AWayThrough.NotRuledOut(notAsked) : new AWayThrough.RuledOut();
    }

    private static AWayThrough notAsked(WhyNotTaken why) {
        return new AWayThrough.NotRuledOut(List.of(why));
    }

    private static AWayThrough incomplete(WhyNotTaken.Shape shape) {
        return notAsked(new WhyNotTaken.ProjectionIncomplete(shape));
    }

    /** Whether the rules leave a value at which {@code relation} holds, or fails where
     *  {@code holds} is false. */
    private static AWayThrough leaves(Relation relation, boolean holds, Quantities rules) {
        Rel asked = holds ? relation.proposition() : relation.proposition().denied();
        return switch (relation) {
            case Relation.Ordered(DecisionAtom.OfTheInput(NumericTerm term), var at, Rel _) ->
                    someValue(rules.runsBetween(term), asked, at) ? LEFT
                            : new AWayThrough.RuledOut();
            case Relation.Ordered _ -> incomplete(WhyNotTaken.Shape.A_NUMBER_A_DEPENDENCY_ANSWERED);
            case Relation.Affine affine -> {
                LinearForm<NumericTerm> form = ofTheInput(affine.form());
                if (form == null) {
                    yield new AWayThrough.NotRuledOut(
                            WhyNotTaken.quantitiesNoRowWrites(affine.form()));
                }
                yield someValue(rules.runsBetween(form), asked, Count.ZERO) ? LEFT
                        : new AWayThrough.RuledOut();
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
