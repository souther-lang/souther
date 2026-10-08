package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Quantities;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Rel;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * Whether some input the rules admit brings what a condition states out one way.
 *
 * <p>Asked of the proposition and not of how the condition was written, so two spellings of one
 * condition leave the same ways. A relation over numbers of the input is asked of the run of
 * values the rules leave the number, and a way stands where some value of that run falls on the
 * side the way needs.
 *
 * <p><b>No is a proof and yes is not.</b> A way is ruled out only where the rules leave no value
 * behind it. Everything else is answered yes: a part nothing read, a quantity of something other
 * than the input, a statement about which case a value is, an element of a container. A
 * conjunction is ruled out where one of its parts is, and a disjunction where every part is — each
 * part asked on its own, which is weaker than asking them together and never wrong the other way.
 */
public final class WhatTheRulesLeave {

    private WhatTheRulesLeave() {}

    /** Whether the rules leave some input on which {@code stated} comes out {@code want}. */
    public static boolean admits(Proposition stated, boolean want, Quantities rules) {
        return switch (stated) {
            case Proposition.Always always -> always.holds() == want;
            case Proposition.Compared compared ->
                    leaves(compared.relation(), compared.holds() == want, rules);
            case Proposition.All all -> want
                    ? all.parts().stream().allMatch(part -> admits(part, true, rules))
                    : all.parts().stream().anyMatch(part -> admits(part, false, rules));
            case Proposition.Any any -> want
                    ? any.parts().stream().anyMatch(part -> admits(part, true, rules))
                    : any.parts().stream().allMatch(part -> admits(part, false, rules));
            default -> true;
        };
    }

    /** Whether the rules leave a value at which {@code relation} holds, or fails where
     *  {@code holds} is false. */
    private static boolean leaves(Relation relation, boolean holds, Quantities rules) {
        Rel asked = holds ? relation.proposition() : relation.proposition().denied();
        return switch (relation) {
            case Relation.Ordered ordered -> !(ordered.term() instanceof DecisionAtom.OfTheInput(
                    NumericTerm term))
                    || someValue(rules.runsBetween(term), asked, ordered.at());
            case Relation.Affine affine -> {
                LinearForm<NumericTerm> form = ofTheInput(affine.form());
                yield form == null || someValue(rules.runsBetween(form), asked, Count.ZERO);
            }
        };
    }

    /** {@code form} as one over numbers of the input, or null where a quantity is something else. */
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
