package souther.compiler.check;

import souther.compiler.diag.SourcePos;
import souther.compiler.inputs.TermPath;
import souther.compiler.inputs.Unsettlement;
import souther.compiler.meaning.WhyNotTaken;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.reach.PathDecision;
import souther.compiler.reach.Proof;
import souther.compiler.reach.WhyUnsettled;
import souther.compiler.types.TypeSymbol;
import souther.compiler.values.Value;
import souther.compiler.values.ValueSet;

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
                                                         ValueSet.Finite named,
                                                         PathDecision departure) {
                return List.of();
            }

            @Override
            public List<PathDecision> everyCaseRefused(String position, List<TypeSymbol> cases) {
                return List.of();
            }

            @Override
            public List<PathDecision> noCaseTheValueCanBeIsTaken(List<TypeSymbol> canBe,
                                                                 List<TypeSymbol> cases) {
                return List.of();
            }

            @Override
            public List<PathDecision> theDeclarationHoldsNoneOf(String position,
                                                                List<TypeSymbol> declared,
                                                                List<TypeSymbol> cases) {
                return List.of();
            }

            @Override
            public List<PathDecision> theDeclarationHoldsNothingElse(String position,
                                                                     List<TypeSymbol> declared,
                                                                     List<TypeSymbol> cases) {
                return List.of();
            }

            @Override
            public List<PathDecision> everyWayInIsRuledOut(List<Proof> each) {
                return List.of();
            }

            @Override
            public List<PathDecision> itsClosureIsAppliedToNothing(List<String> containers,
                                                                   List<PathDecision> decisions) {
                return decisions;
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
                                                       ValueSet.Finite named,
                                                       PathDecision departure) {
                return List.of();
            }

            @Override
            public List<TypeSymbol> everyCaseRefused(String position, List<TypeSymbol> cases) {
                return cases;
            }

            @Override
            public List<TypeSymbol> noCaseTheValueCanBeIsTaken(List<TypeSymbol> canBe,
                                                               List<TypeSymbol> cases) {
                return List.of();
            }

            @Override
            public List<TypeSymbol> theDeclarationHoldsNoneOf(String position,
                                                              List<TypeSymbol> declared,
                                                              List<TypeSymbol> cases) {
                return List.of();
            }

            @Override
            public List<TypeSymbol> theDeclarationHoldsNothingElse(String position,
                                                                   List<TypeSymbol> declared,
                                                                   List<TypeSymbol> cases) {
                return List.of();
            }

            @Override
            public List<TypeSymbol> everyWayInIsRuledOut(List<Proof> each) {
                return List.of();
            }

            @Override
            public List<TypeSymbol> itsClosureIsAppliedToNothing(List<String> containers,
                                                                 List<PathDecision> decisions) {
                return List.of();
            }
        });
    }

    /** One value a rule names, as its own content: a number at its digits, a text as it is. */
    private static String valueOf(Value value) {
        return switch (value) {
            case Value.Number number -> number.value().toPlainString();
            case Value.Text text -> text.value();
            case Value.Truth truth -> Boolean.toString(truth.value());
            case Value.Case one -> one.data().name();
        };
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
                                             ValueSet.Finite named, PathDecision departure) {
                // The ends and the values and not a rendering of them: how a report words either
                // is the renderer's, and a test asserting on that would be asserting on it twice.
                // Each where the proof holds it, which is one or both.
                return position
                        + (admits == null ? "" : " "
                                + (admits.min() == null ? "" : admits.min().at()) + ".."
                                + (admits.max() == null ? "" : admits.max().at()))
                        + (named == null ? "" : " " + named.values().stream()
                                .map(WhatAnAnswerSays::valueOf).toList());
            }

            @Override
            public String everyCaseRefused(String position, List<TypeSymbol> cases) {
                return null;
            }

            @Override
            public String noCaseTheValueCanBeIsTaken(List<TypeSymbol> canBe,
                                                     List<TypeSymbol> cases) {
                return null;
            }

            @Override
            public String theDeclarationHoldsNoneOf(String position, List<TypeSymbol> declared,
                                                    List<TypeSymbol> cases) {
                return null;
            }

            @Override
            public String theDeclarationHoldsNothingElse(String position,
                                                         List<TypeSymbol> declared,
                                                         List<TypeSymbol> cases) {
                return null;
            }

            @Override
            public String everyWayInIsRuledOut(List<Proof> each) {
                return null;
            }

            @Override
            public String itsClosureIsAppliedToNothing(List<String> containers,
                                                       List<PathDecision> decisions) {
                return null;
            }
        });
    }

    /** The containers a proof says the closure the place is in is applied over and no rule leaves
     *  an element, or none where the proof says something else. */
    static List<String> containersAppliedToNothingIn(Proof proof) {
        return proof.said(new Proof.Words<List<String>>() {

            @Override
            public List<String> conditionsThatCannotAllHold(List<PathDecision> decisions) {
                return List.of();
            }

            @Override
            public List<String> outsideInputDomain(TermPath position,
                                                   NumericDomain.Bounds admits,
                                                   ValueSet.Finite named,
                                                   PathDecision departure) {
                return List.of();
            }

            @Override
            public List<String> everyCaseRefused(String position, List<TypeSymbol> cases) {
                return List.of();
            }

            @Override
            public List<String> noCaseTheValueCanBeIsTaken(List<TypeSymbol> canBe,
                                                           List<TypeSymbol> cases) {
                return List.of();
            }

            @Override
            public List<String> theDeclarationHoldsNoneOf(String position,
                                                          List<TypeSymbol> declared,
                                                          List<TypeSymbol> cases) {
                return List.of();
            }

            @Override
            public List<String> theDeclarationHoldsNothingElse(String position,
                                                               List<TypeSymbol> declared,
                                                               List<TypeSymbol> cases) {
                return List.of();
            }

            @Override
            public List<String> everyWayInIsRuledOut(List<Proof> each) {
                return List.of();
            }

            @Override
            public List<String> itsClosureIsAppliedToNothing(List<String> containers,
                                                             List<PathDecision> decisions) {
                return containers;
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
            public Boolean aConditionWasNotRead(SourcePos at, List<WhyNotTaken> why) {
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
