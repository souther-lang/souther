package souther.compiler.meaning;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;

import java.util.List;

/**
 * Whether a statement read of one node says the same of any node it is moved to: every place it
 * names is under the node, which is the node's own and moves with it, or under one of the places
 * that stay where they are wherever the node is, and none of those is under the node or holds it.
 *
 * <p>Where a place that stays put is under the node, or holds it, one place could be read as the
 * node's or as the one that stays, and moving the node would move a part of what it was compared
 * with. A value a body bound or a dependency answered is made from something nothing here names,
 * so a statement naming one is not moved anywhere; nor is one holding a part nothing read, or a
 * search of its own.
 */
public final class WrittenOfANode {

    private final TermPath node;
    private final List<TermPath> staying;

    private WrittenOfANode(TermPath node, List<TermPath> staying) {
        this.node = node;
        this.staying = staying;
    }

    /**
     * Whether a place that stays put at {@code stays} is apart from the node at {@code node}:
     * neither under the other. Asked of the places before anything is read of the node, since it
     * turns on nothing else.
     */
    public static boolean apart(TermPath stays, TermPath node) {
        return !stays.isAtOrUnder(node) && !node.isAtOrUnder(stays);
    }

    /** Whether {@code stated}, read of the node at {@code node}, says the same of any node. */
    public static boolean movesWithIt(Proposition stated, TermPath node, List<TermPath> staying) {
        for (TermPath stays : staying) {
            if (!apart(stays, node)) {
                return false;
            }
        }
        return new WrittenOfANode(node, List.copyOf(staying)).reads(stated);
    }

    private boolean reads(Proposition stated) {
        return switch (stated) {
            case Proposition.Always _ -> true;
            case Proposition.Unread _, Proposition.SomeReachable _, Proposition.Carried _ -> false;
            case Proposition.Compared compared -> switch (compared.relation()) {
                case Relation.Affine affine -> affine.form().coefs().keySet().stream()
                        .allMatch(this::reads);
                case Relation.Ordered ordered -> reads(ordered.term());
            };
            case Proposition.Truth truth -> reads(truth.of());
            case Proposition.InCases cases -> reads(cases.of());
            case Proposition.Present present -> reads(present.of());
            case Proposition.SameValue same -> reads(same.one()) && reads(same.other());
            case Proposition.LastToHold last -> reads(last.container()) && reads(last.position());
            case Proposition.All all -> all.parts().stream().allMatch(this::reads);
            case Proposition.Any any -> any.parts().stream().allMatch(this::reads);
            case Proposition.WhereItAnswers where ->
                    reads(where.answers()) && reads(where.states());
            case Proposition.OnAnApplication applications ->
                    applications.each().stream().allMatch(this::reads);
            case Proposition.SoManyHold counted -> counted.statements().stream()
                    .allMatch(this::reads);
            case Proposition.Some some -> reads(some.container()) && reads(some.ofTheElement());
        };
    }

    private boolean reads(Quantity quantity) {
        return switch (quantity) {
            case DecisionAtom.OfTheInput(NumericTerm term) -> reads(term);
            case DecisionAtom.OfAnAnswer _, DecisionAtom.TakenOfAnAnswer _, Quantity.OfABinding _,
                 Quantity.CodePointsOfAPiece _, Quantity.HowManyCarried _ -> false;
            case Quantity.HowManyMeet count -> reads(count.container())
                    && reads(count.ofTheElement());
            case Quantity.HowManyHold held -> held.each().stream().allMatch(this::reads);
            case Quantity.HowManyDifferent different -> reads(different.container())
                    && reads(different.ofTheElement());
            case Quantity.SumOver sum -> reads(sum.container()) && reads(sum.ofTheElement());
            case Quantity.RemainderOfADividend remainder -> remainder.dividend().coefs().keySet()
                    .stream().allMatch(this::reads);
            case Quantity.ProductOfTwo product -> product.factors().stream().allMatch(this::reads);
            case Quantity.WhatAnOperationAnswers answers -> answers.of().stream()
                    .allMatch(this::reads);
        };
    }

    /** Whether every place {@code term} is read off is the node's or stays put. */
    private boolean reads(NumericTerm term) {
        return term.placesReadOff().stream().allMatch(this::reads);
    }

    private boolean reads(DecisionSubject subject) {
        return subject instanceof DecisionSubject.AnInput(TermPath at) && reads(at);
    }

    private boolean reads(TermPath at) {
        return at.isAtOrUnder(node) || staying.stream().anyMatch(at::isAtOrUnder);
    }
}
