package souther.compiler.meaning;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;

import java.util.Collections;
import java.util.IdentityHashMap;
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
    /** Whether a value a binding holds is read as itself rather than as nothing a place is. */
    private final boolean valuesBound;
    private final Set<Quantity.OfABinding> bound = new LinkedHashSet<>();
    /** The answers of operations already read, by identity: one held by several others is read once
     *  however many paths lead to it. */
    private final Set<Quantity.WhatAnOperationAnswers> answersRead =
            Collections.newSetFromMap(new IdentityHashMap<>());
    /** How many applications of a closure the part read is inside. */
    private int insideAnApplication;

    /** Whether a value a binding holds is read as the places what it is handed is of. */
    private final boolean handedOff;

    private PositionsAStatementReads(boolean answersNameNothing, boolean everyPlace) {
        this(answersNameNothing, everyPlace, false);
    }

    private PositionsAStatementReads(boolean answersNameNothing, boolean everyPlace,
                                     boolean valuesBound) {
        this(answersNameNothing, everyPlace, valuesBound, false);
    }

    private PositionsAStatementReads(boolean answersNameNothing, boolean everyPlace,
                                     boolean valuesBound, boolean handedOff) {
        this.answersNameNothing = answersNameNothing;
        this.everyPlace = everyPlace;
        this.valuesBound = valuesBound;
        this.handedOff = handedOff;
    }

    /**
     * What a statement reads: a place of the input, or a value a binding holds.
     *
     * <p>Which a statement names and nothing more. Two of these that are not equal are not shown
     * to be two values: a value a binding holds may be a number some place holds, and the same
     * binding may hold one value on one application and another on the next. Whether two of them
     * are one value, or two, is asked of what they denote, and not of these.
     */
    public sealed interface ReadSubject {

        /** A place of the input. */
        record At(TermPath path) implements ReadSubject {}

        /** A value a binding holds where the statement is read, outside every application of a
         *  closure the statement is about. */
        record Bound(Quantity.OfABinding value) implements ReadSubject {}

        /**
         * Whether something asked of what {@code one} reads can say something of what
         * {@code other} reads — the one answer to whether two of them are apart.
         *
         * <p>Where either is not known (null) it may read anything. A value a binding holds is
         * about every place: what it is held to — the list it is an element of, the places it was
         * worked out of — is nothing a statement need say. Two places bear on each other where
         * one stands at, under or around the other, narrowings to cases aside
         * ({@link TermPath#bearsOn}).
         */
        static boolean bearOnEachOther(Set<ReadSubject> one, Set<ReadSubject> other) {
            if (one == null || other == null) {
                return true;
            }
            if (one.stream().anyMatch(Bound.class::isInstance)
                    || other.stream().anyMatch(Bound.class::isInstance)) {
                return true;
            }
            for (ReadSubject here : one) {
                for (ReadSubject there : other) {
                    if (here instanceof At(TermPath at) && there instanceof At(TermPath to)
                            && at.bearsOn(to)) {
                        return true;
                    }
                }
            }
            return false;
        }
    }

    /**
     * Every place {@code stated} is read off ({@link #everyPlaceOf}) and every value a binding
     * holds that it reads outside every application of a closure it states something of — or
     * empty where it reads anything else, a value bound inside one of those included: a name a
     * closure binds holds what each application hands it, and is one value only on one
     * application.
     */
    public static Optional<Set<ReadSubject>> everyPlaceAndValueOf(Proposition stated) {
        PositionsAStatementReads reading = new PositionsAStatementReads(false, true, true);
        if (!reading.reads(stated)) {
            return Optional.empty();
        }
        Set<ReadSubject> out = new LinkedHashSet<>();
        reading.out.forEach(path -> out.add(new ReadSubject.At(path)));
        reading.bound.forEach(value -> out.add(new ReadSubject.Bound(value)));
        return Optional.of(Collections.unmodifiableSet(out));
    }

    /**
     * Every place each number {@code quantity} is read off ({@link NumericTerm#placesReadOff}) —
     * both factors of a product, and not only the one it is filed under — and each value a binding
     * holds that it reads, the places first; or empty where it reads anything else: an answer,
     * what a walk carried, a piece of a string.
     */
    public static Optional<Set<ReadSubject>> ofANumber(Quantity quantity) {
        PositionsAStatementReads reading = new PositionsAStatementReads(false, true, true);
        if (!reading.reads(quantity)) {
            return Optional.empty();
        }
        Set<ReadSubject> out = new LinkedHashSet<>();
        reading.out.forEach(path -> out.add(new ReadSubject.At(path)));
        reading.bound.forEach(value -> out.add(new ReadSubject.Bound(value)));
        return Optional.of(Collections.unmodifiableSet(out));
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
     * Every place {@code stated} turns on: those it is read off ({@link #everyPlaceOf}), and for a
     * value a binding holds the places what the binding was handed is of — the two ends of the
     * whole numbers a walk is handed, the container a walk walks and how many it holds, or the
     * container an index picks in. Empty where it reads anything else, a value bound that was
     * handed nothing included: that value may turn on any place.
     */
    public static Optional<List<TermPath>> everyPlaceItTurnsOn(Proposition stated) {
        PositionsAStatementReads reading =
                new PositionsAStatementReads(false, true, false, true);
        return reading.reads(stated) ? Optional.of(List.copyOf(reading.out)) : Optional.empty();
    }

    /** The places a value handed to a step is of, or false where it is handed nothing that says. */
    private boolean readsWhatIsHanded(Quantity.OfABinding value) {
        if (value.handed().isEmpty()) {
            return false;
        }
        return switch (value.handed().get()) {
            case Quantity.AWholeNumberInTurn(var from, var to) -> {
                from.coefs().keySet().forEach(term -> out.addAll(term.placesReadOff()));
                to.coefs().keySet().forEach(term -> out.addAll(term.placesReadOff()));
                yield true;
            }
            case Quantity.PositionInTheWalk(TermPath container, var howMany) -> {
                out.add(container);
                out.addAll(howMany.placesReadOff());
                yield true;
            }
            case Quantity.PickedAtAnIndex(TermPath container, long _, TermPath element,
                                          var howMany) -> {
                out.add(container);
                out.add(element);
                out.addAll(howMany.placesReadOff());
                yield true;
            }
            case Quantity.KeptSoFar _ -> false;
        };
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
                    Proposition.InTheStrings.Strings.AtAPosition(TermPath at,
                            ValueIdentity identity), var _, var _,
                    var _) -> reads(new DecisionSubject.AnInput(at, identity));
            // A piece is whatever the statement it is read inside says it is, and the string that
            // statement is about is no part of this statement to collect.
            case Proposition.InTheStrings _ -> false;
            // Against a value written, what is read is the one subject alone.
            case Proposition.SameValue same -> reads(same.one())
                    && (same.otherSubject() == null || reads(same.otherSubject()));
            case Proposition.StringInside inside -> reads(inside.inner()) && reads(inside.outer());
            case Proposition.LastToHold last -> reads(last.container()) && reads(last.position());
            case Proposition.OnAnApplication _ -> {
                insideAnApplication++;
                boolean read = stated.partsHeld().stream().allMatch(this::reads);
                insideAnApplication--;
                yield read;
            }
            case Proposition.All _, Proposition.Any _, Proposition.WhereItAnswers _,
                 Proposition.SoManyHold _,
                 Proposition.OfTheWays _ -> stated.partsHeld().stream().allMatch(this::reads);
            case Proposition.Some some -> reads(some.container()) && reads(some.ofTheElement());
        };
    }

    private boolean reads(Quantity quantity) {
        return switch (quantity) {
            case DecisionAtom.OfTheInput(var term, var _) -> reads(term);
            case DecisionAtom.OfAnAnswer _, DecisionAtom.TakenOfAnAnswer _,
                 DecisionAtom.ComputedOverAnAnswer _ -> answersNameNothing;
            case Quantity.OfABinding value -> handedOff ? readsWhatIsHanded(value)
                    : valuesBound && insideAnApplication == 0 && kept(value);
            case Quantity.HowManyCarried _, Quantity.TheKeptTotal _ -> false;
            // Each distinct answer once: what it adds is the positions of the inputs it is made of,
            // which a second visit adds again to a set, and what it answers is that of each one.
            case Quantity.WhatAnOperationAnswers answers -> !answersRead.add(answers)
                    || answers.of().stream().allMatch(this::reads);
            // A piece of a string is whatever the statement it is read inside says it is, and the
            // string that statement is about is no part of this quantity to collect.
            case Quantity.CodePointsOfAPiece _ -> false;
            case Quantity.APieceOf piece -> reads(piece.string());
            case Quantity.ThePieceAt piece -> reads(piece.string());
            case Quantity.IsAmongThePieces among -> reads(among.value()) && reads(among.string());
            case Quantity.HowManyMeet(DecisionSubject counted, Proposition each) ->
                    reads(counted) && reads(each);
            case Quantity.HowManyMeetAcross(DecisionSubject counted, DecisionSubject inner,
                                            Proposition each) ->
                    reads(counted) && reads(inner) && reads(each);
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

    /** {@code value} kept among what the statement reads, which is then read. */
    private boolean kept(Quantity.OfABinding value) {
        bound.add(value);
        return true;
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
            case DecisionSubject.AnInput(TermPath at, var _) -> {
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
