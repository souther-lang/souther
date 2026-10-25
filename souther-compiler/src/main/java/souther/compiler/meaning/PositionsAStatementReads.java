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
 *
 * <p>Or the positions it names beside what a dependency answered ({@link #besideAnAnswer}): an
 * answer is a value nothing relates to the input, so a statement about it narrows which answer a
 * row stands the dependency in with and leaves the input's values as they were, but at the
 * positions it names beside the answer.
 */
public final class PositionsAStatementReads {

    /** Where the positions go, and whether an answer is read as naming nothing of the input. */
    private final Set<TermPath> out = new LinkedHashSet<>();
    private final boolean answersNameNothing;
    private final boolean everyPlace;

    private PositionsAStatementReads(boolean answersNameNothing, boolean everyPlace) {
        this.answersNameNothing = answersNameNothing;
        this.everyPlace = everyPlace;
    }

    /** The positions {@code stated} reads, in the order it names them, or empty where it reads
     *  something else as well. */
    public static Optional<List<TermPath>> of(Proposition stated) {
        PositionsAStatementReads reading = new PositionsAStatementReads(false, false);
        return reading.reads(stated) ? Optional.of(List.copyOf(reading.out)) : Optional.empty();
    }

    /**
     * Every place {@code stated} is read off, in the order it names them — each place a number is
     * read off ({@link NumericTerm#placesReadOff}) and not only the one it is filed under — or
     * empty where it reads something that is no place. Whatever the statement says of an element
     * stands at some of these places, and a form of statement this does not know is empty rather
     * than silent, so that no question asked of the places leaves one unasked.
     */
    public static Optional<List<TermPath>> everyPlaceOf(Proposition stated) {
        PositionsAStatementReads reading = new PositionsAStatementReads(false, true);
        return reading.reads(stated) ? Optional.of(List.copyOf(reading.out)) : Optional.empty();
    }

    /**
     * The positions of the input {@code stated} names beside what a dependency answered, in the
     * order it names them — or empty where it reads something that is neither, or is about no
     * answer at all.
     */
    public static Optional<List<TermPath>> besideAnAnswer(Proposition stated) {
        if (!Proposition.aboutAnAnswer(stated)) {
            return Optional.empty();
        }
        PositionsAStatementReads reading = new PositionsAStatementReads(true, false);
        return reading.reads(stated) ? Optional.of(List.copyOf(reading.out)) : Optional.empty();
    }

    private boolean reads(Proposition stated) {
        return switch (stated) {
            case Proposition.Always _ -> true;
            case Proposition.Carried _, Proposition.Unread _, Proposition.SomeReachable _ -> false;
            case Proposition.Compared compared -> switch (compared.relation()) {
                case Relation.Affine affine -> affine.form().coefs().keySet().stream()
                        .allMatch(this::reads);
                case Relation.Ordered ordered -> reads(ordered.term());
            };
            case Proposition.Truth truth -> reads(truth.of());
            case Proposition.InCases cases -> reads(cases.of());
            case Proposition.Present present -> reads(present.of());
            case Proposition.InTheStrings(
                    Proposition.InTheStrings.Strings.AtAPosition(TermPath at), var _, var _,
                    var _) -> reads(new DecisionSubject.AnInput(at));
            // A piece is whatever the statement it is read inside says it is, and the string that
            // statement is about is no part of this statement to collect.
            case Proposition.InTheStrings _ -> false;
            case Proposition.SameValue same -> reads(same.one()) && reads(same.other());
            case Proposition.LastToHold last -> reads(last.container()) && reads(last.position());
            case Proposition.All all -> all.parts().stream().allMatch(this::reads);
            case Proposition.WhereItAnswers where ->
                    reads(where.answers()) && reads(where.states());
            case Proposition.Any any -> any.parts().stream().allMatch(this::reads);
            case Proposition.OnAnApplication applications -> applications.each().stream()
                    .allMatch(this::reads);
            case Proposition.SoManyHold counted -> counted.statements().stream()
                    .allMatch(this::reads);
            case Proposition.Some some -> reads(some.container()) && reads(some.ofTheElement());
        };
    }

    private boolean reads(Quantity quantity) {
        return switch (quantity) {
            case DecisionAtom.OfTheInput(var term) -> reads(term);
            case DecisionAtom.OfAnAnswer _, DecisionAtom.TakenOfAnAnswer _,
                 DecisionAtom.ComputedOverAnAnswer _ -> answersNameNothing;
            case Quantity.OfABinding _, Quantity.HowManyCarried _ -> false;
            case Quantity.WhatAnOperationAnswers answers -> answers.of().stream()
                    .allMatch(this::reads);
            // A piece of a string is whatever the statement it is read inside says it is, and the
            // string that statement is about is no part of this quantity to collect.
            case Quantity.CodePointsOfAPiece _ -> false;
            case Quantity.APieceOf piece -> reads(piece.string());
            case Quantity.IsAmongThePieces among -> reads(among.value()) && reads(among.string());
            case Quantity.HowManyMeet(DecisionSubject counted, Proposition each) ->
                    reads(counted) && reads(each);
            case Quantity.HowManyHold(List<Proposition> each) -> each.stream()
                    .allMatch(this::reads);
            case Quantity.HowManyDifferent(DecisionSubject counted, Quantity.TheValue each) ->
                    reads(counted) && reads(each);
            case Quantity.HowManyDifferentMeet(DecisionSubject counted, Quantity.TheValue each,
                                               var meeting) ->
                    reads(counted) && reads(each) && reads(meeting.statement());
            case Quantity.HowManyDifferentAcross(DecisionSubject counted, DecisionSubject each) ->
                    reads(counted) && reads(each);
            case Quantity.HowManyDifferentBelow below -> {
                out.add(below.root());
                out.add(below.keyOfTheRoot());
                out.add(below.map());
                out.add(below.map().key());
                out.add(below.valueOfAnEntry());
                yield true;
            }
            case Quantity.SumOver(DecisionSubject summed, Quantity each) ->
                    reads(summed) && reads(each);
            case Quantity.RemainderOfADividend(var _, var dividend, var _) ->
                    dividend.coefs().keySet().stream().allMatch(this::reads);
            case Quantity.RemainderByAnInput remainder -> remainder.operands().stream()
                    .allMatch(this::reads);
            case Quantity.ProductOfTwo product -> product.factors().stream()
                    .allMatch(this::reads);
        };
    }

    private boolean reads(NumericTerm term) {
        if (everyPlace) {
            out.addAll(term.placesReadOff());
        } else {
            out.add(term.subjectPath());
        }
        return true;
    }
    private boolean reads(DecisionSubject subject) {
        return switch (subject) {
            case DecisionSubject.AnInput(TermPath at) -> {
                out.add(at);
                yield true;
            }
            case DecisionSubject.AnAnswer _ -> answersNameNothing;
        };
    }

    /** Where a value counted once each stands: the place, or every place its case is told and
     *  read at. */
    private boolean reads(Quantity.TheValue value) {
        return switch (value) {
            case Quantity.TheValue.AtAPlace(DecisionSubject at) -> reads(at);
            case Quantity.TheValue.ChosenByCase chosen -> {
                out.addAll(chosen.places());
                yield true;
            }
        };
    }
}
