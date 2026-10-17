package souther.compiler.meaning;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;

/**
 * The positions of the input a proposition reads, where it reads nothing else.
 *
 * <p>What a fork turns on, where the fork's own tree could not name it: a condition that is the
 * answer of an operation over a container — {@code List.all(...)} — is no position, and what the
 * operation states of it is. Every position it names is one the fork may tell values apart at, and
 * none other is.
 *
 * <p>Empty where any part reads something no position is — an answer, a value the body bound, what
 * a walk carried, a part nothing read — since the fork may then turn on any position at all.
 */
public final class PositionsAStatementReads {

    private PositionsAStatementReads() {}

    /** The positions {@code stated} reads, in the order it names them, or empty where it reads
     *  something else as well. */
    public static Optional<List<TermPath>> of(Proposition stated) {
        Set<TermPath> out = new LinkedHashSet<>();
        return reads(stated, out) ? Optional.of(List.copyOf(out)) : Optional.empty();
    }

    private static boolean reads(Proposition stated, Set<TermPath> out) {
        return switch (stated) {
            case Proposition.Always _ -> true;
            case Proposition.Carried _, Proposition.Unread _, Proposition.SomeReachable _ -> false;
            case Proposition.Compared compared -> switch (compared.relation()) {
                case Relation.Affine affine -> affine.form().coefs().keySet().stream()
                        .allMatch(quantity -> reads(quantity, out));
                case Relation.Ordered ordered -> reads(ordered.term(), out);
            };
            case Proposition.Truth truth -> reads(truth.of(), out);
            case Proposition.InCases cases -> reads(cases.of(), out);
            case Proposition.Present present -> reads(present.of(), out);
            case Proposition.SameValue same -> reads(same.one(), out) && reads(same.other(), out);
            case Proposition.LastToHold last -> {
                out.add(last.container());
                out.add(last.position());
                yield true;
            }
            case Proposition.All all -> all.parts().stream().allMatch(part -> reads(part, out));
            case Proposition.Any any -> any.parts().stream().allMatch(part -> reads(part, out));
            case Proposition.OnAnApplication applications -> applications.each().stream()
                    .allMatch(one -> reads(one, out));
            case Proposition.SoManyHold counted -> counted.statements().stream()
                    .allMatch(one -> reads(one, out));
            case Proposition.Some some -> reads(some.container(), out)
                    && reads(some.ofTheElement(), out);
        };
    }

    private static boolean reads(Quantity quantity, Set<TermPath> out) {
        return switch (quantity) {
            case DecisionAtom.OfTheInput(var term) -> reads(term, out);
            case DecisionAtom.OfAnAnswer _, DecisionAtom.TakenOfAnAnswer _,
                 Quantity.OfABinding _, Quantity.HowManyCarried _ -> false;
            case Quantity.WhatAnOperationAnswers answers -> answers.of().stream()
                    .allMatch(each -> reads(each, out));
            // A piece of a string is whatever the statement it is read inside says it is, and the
            // string that statement is about is no part of this quantity to collect.
            case Quantity.CodePointsOfAPiece _ -> false;
            case Quantity.HowManyMeet(DecisionSubject counted, Proposition each) ->
                    reads(counted, out) && reads(each, out);
            case Quantity.HowManyHold(List<Proposition> each) -> each.stream()
                    .allMatch(one -> reads(one, out));
            case Quantity.HowManyDifferent(DecisionSubject counted, DecisionSubject each) ->
                    reads(counted, out) && reads(each, out);
            case Quantity.SumOver(DecisionSubject summed, Quantity each) ->
                    reads(summed, out) && reads(each, out);
            case Quantity.RemainderOfADividend(var _, var dividend, var _) ->
                    dividend.coefs().keySet().stream().allMatch(term -> reads(term, out));
            case Quantity.ProductOfTwo product -> product.factors().stream()
                    .allMatch(term -> reads(term, out));
        };
    }

    private static boolean reads(NumericTerm term, Set<TermPath> out) {
        out.add(term.subjectPath());
        return true;
    }

    private static boolean reads(DecisionSubject subject, Set<TermPath> out) {
        return switch (subject) {
            case DecisionSubject.AnInput(TermPath at) -> {
                out.add(at);
                yield true;
            }
            case DecisionSubject.AnAnswer _ -> false;
        };
    }
}
