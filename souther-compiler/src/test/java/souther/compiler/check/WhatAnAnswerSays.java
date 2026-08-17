package souther.compiler.check;

import souther.compiler.diag.SourcePos;
import souther.compiler.inputs.TermPath;
import souther.compiler.inputs.Unsettlement;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.reach.PathDecision;
import souther.compiler.reach.Proof;
import souther.compiler.reach.WhyUnsettled;
import souther.compiler.types.TypeSymbol;

import java.util.List;

/**
 * What a test reads off a proof or a reason, said the one way there is to say it.
 *
 * <p>A test is a reader like any other, and the arms are not types it can name either. So it asks
 * the same way the renderer does — which is also what keeps a test from asserting on a distinction
 * nothing writes a sentence about.
 */
final class WhatAnAnswerSays {

    private WhatAnAnswerSays() {}

    /** The conditions a proof rests on, or none where it rests on something else. */
    static List<PathDecision> conditionsIn(Proof proof) {
        return proof.said(new Proof.Words<List<PathDecision>>() {

            @Override
            public List<PathDecision> conditionsThatCannotAllHold(List<PathDecision> decisions) {
                return decisions;
            }

            @Override
            public List<PathDecision> outsideInputDomain(TermPath position,
                                                         NumericDomain.Bounds admits,
                                                         PathDecision departure) {
                return List.of();
            }

            @Override
            public List<PathDecision> everyCaseRefused(String position, List<TypeSymbol> cases) {
                return List.of();
            }
        });
    }

    /** The cases a proof refuses, or none where it is not that kind of proof. */
    static List<TypeSymbol> casesRefusedIn(Proof proof) {
        return proof.said(new Proof.Words<List<TypeSymbol>>() {

            @Override
            public List<TypeSymbol> conditionsThatCannotAllHold(List<PathDecision> decisions) {
                return List.of();
            }

            @Override
            public List<TypeSymbol> outsideInputDomain(TermPath position,
                                                       NumericDomain.Bounds admits,
                                                       PathDecision departure) {
                return List.of();
            }

            @Override
            public List<TypeSymbol> everyCaseRefused(String position, List<TypeSymbol> cases) {
                return cases;
            }
        });
    }

    /** Where a proof says the position's own values stop short of the branch, that position and
     *  what it holds — or nothing, where the proof says something else. */
    static String positionOutrunIn(Proof proof) {
        return proof.said(new Proof.Words<String>() {

            @Override
            public String conditionsThatCannotAllHold(List<PathDecision> decisions) {
                return null;
            }

            @Override
            public String outsideInputDomain(TermPath position, NumericDomain.Bounds admits,
                                             PathDecision departure) {
                // The ends and not a rendering of them: how a report words a range is the
                // renderer's, and a test asserting on that would be asserting on it twice.
                return position + " " + admits.min().at() + ".." + admits.max().at();
            }

            @Override
            public String everyCaseRefused(String position, List<TypeSymbol> cases) {
                return null;
            }
        });
    }

    /** Whether the reading could not take the condition in. */
    static boolean isAConditionNotRead(WhyUnsettled why) {
        return why.said(new WhyUnsettled.Words<Boolean>() {

            @Override
            public Boolean noWitness() {
                return false;
            }

            @Override
            public Boolean aConditionWasNotRead(SourcePos at) {
                return true;
            }

            @Override
            public Boolean thePositionDidNotSettleIt(Unsettlement position) {
                return false;
            }

            @Override
            public Boolean theWalkDidNotReachIt() {
                return false;
            }
        });
    }
}
