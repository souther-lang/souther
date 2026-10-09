package souther.compiler.proof;

import souther.compiler.semantics.AnswerAspect;
import souther.compiler.semantics.ElementShape;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.LawSubject;

/**
 * Which constructions of a container a statement about it survives: where the statement held of
 * the container, it holds of what was built from it.
 *
 * <p>Read off the statement's words and nothing else. A statement that reads the container only
 * through which elements it holds and how many times — whether some element meets something, how
 * many do, whether it holds anything, how many it holds — reads the same of the same elements in
 * another order ({@link ElementShape#PERMUTES}). One that reads it only as "no element meets this"
 * or "it holds nothing", and reads none of it by number, holds as well of some of those elements
 * ({@link ElementShape#SUBSET}), since a part of what has no such element has none. A statement
 * reading the container any other way — handing it to another operation, naming where an element
 * is filed — is one nothing is said of here, and survives no construction.
 */
public final class WhatAStatementSurvives {

    private WhatAStatementSurvives() {}

    /** Whether {@code statement}, over arguments by place, survives a construction of the argument
     *  at {@code container} of shape {@code shape}. */
    public static boolean survives(LawProposition<Integer> statement, int container,
                                   ElementShape shape) {
        Reads reads = new Reads(container);
        reads.statement(statement, true);
        return switch (shape) {
            case PERMUTES -> !reads.otherwise;
            case SUBSET -> !reads.otherwise && !reads.byNumber && !reads.growing;
            case MAPS, COLLAPSES -> false;
        };
    }

    /** How a statement reads one container. */
    private static final class Reads {

        private final int container;
        /** Read some way other than by its elements and how many times each. */
        private boolean otherwise;
        /** Read by a number: how many it holds, or how many of its elements meet something. */
        private boolean byNumber;
        /** Read where more elements make the statement truer: some element meeting something,
         *  or its holding anything, taken as it stands rather than denied. */
        private boolean growing;

        Reads(int container) {
            this.container = container;
        }

        /** Reads {@code statement}, standing as it is where {@code upright} and denied where
         *  not. */
        void statement(LawProposition<Integer> statement, boolean upright) {
            switch (statement) {
                case LawProposition.Always<Integer> _ -> { }
                case LawProposition.All<Integer>(var parts) ->
                        parts.forEach(part -> statement(part, upright));
                case LawProposition.Any<Integer>(var parts) ->
                        parts.forEach(part -> statement(part, upright));
                case LawProposition.Observed<Integer>(LawSubject<Integer> of, var side) -> {
                    if (of instanceof LawSubject.Argument<Integer>(Integer at) && at == container
                            && side.aspect() == AnswerAspect.EMPTINESS) {
                        growing |= upright == side.holds();
                    } else {
                        subject(of, false);
                    }
                }
                case LawProposition.Compared<Integer>(var form, var _) ->
                        form.coefs().keySet().forEach(this::number);
                case LawProposition.SomeElement<Integer>(Integer over, var ofTheElement,
                                                         boolean holds) -> {
                    if (over == container) {
                        growing |= upright == holds;
                        element(ofTheElement);
                    } else {
                        statement(ofTheElement, upright == holds);
                    }
                }
                case LawProposition.Same<Integer>(var one, var other, var _) -> {
                    subject(one, false);
                    subject(other, false);
                }
            }
        }

        /** Reads a statement about one element of the container. */
        private void element(LawProposition<Integer> ofTheElement) {
            Reads inside = new Reads(container);
            inside.withinAnElement(ofTheElement);
            otherwise |= inside.otherwise;
        }

        /** Reads a statement inside a quantifier over the container, where the element is the
         *  container's to name and nothing else of it is. */
        private void withinAnElement(LawProposition<Integer> statement) {
            switch (statement) {
                case LawProposition.Always<Integer> _ -> { }
                case LawProposition.All<Integer>(var parts) -> parts.forEach(this::withinAnElement);
                case LawProposition.Any<Integer>(var parts) -> parts.forEach(this::withinAnElement);
                case LawProposition.Observed<Integer>(var of, var _) -> subject(of, true);
                case LawProposition.Compared<Integer>(var form, var _) ->
                        form.coefs().keySet().forEach(number -> {
                            if (number instanceof LawNumber.AnArgument<Integer>(Integer at)
                                    && at == container
                                    || number instanceof LawNumber.HowManyMeet<Integer>(
                                            Integer over, var _) && over == container) {
                                otherwise = true;
                            } else if (number instanceof LawNumber.SizeOf<Integer>(var of)) {
                                subject(of, true);
                            } else if (number instanceof LawNumber.HowManyMeet<Integer>(
                                    var _, var ofTheElement)) {
                                withinAnElement(ofTheElement);
                            }
                        });
                case LawProposition.SomeElement<Integer>(Integer over, var ofTheElement,
                                                         var _) -> {
                    otherwise |= over == container;
                    withinAnElement(ofTheElement);
                }
                case LawProposition.Same<Integer>(var one, var other, var _) -> {
                    subject(one, true);
                    subject(other, true);
                }
            }
        }

        private void number(LawNumber<Integer> number) {
            switch (number) {
                case LawNumber.AnArgument<Integer>(Integer at) -> otherwise |= at == container;
                case LawNumber.SizeOf<Integer>(LawSubject<Integer> of) -> {
                    if (of instanceof LawSubject.Argument<Integer>(Integer at) && at == container) {
                        byNumber = true;
                    } else {
                        subject(of, false);
                    }
                }
                case LawNumber.HowManyMeet<Integer>(Integer over, var ofTheElement) -> {
                    if (over == container) {
                        byNumber = true;
                        element(ofTheElement);
                    } else {
                        statement(ofTheElement, true);
                        statement(ofTheElement, false);
                    }
                }
            }
        }

        /** Reads a value a statement names, where {@code anElement} says whether an element of
         *  the container is one it may name. */
        private void subject(LawSubject<Integer> subject, boolean anElement) {
            switch (subject) {
                case LawSubject.Argument<Integer>(Integer at) -> otherwise |= at == container;
                case LawSubject.ElementOf<Integer>(Integer of) ->
                        otherwise |= of == container && !anElement;
                case LawSubject.KeyOf<Integer>(Integer of) -> otherwise |= of == container;
                case LawSubject.WhatTheClosureAnswers<Integer>(Integer closure) ->
                        otherwise |= closure == container;
                case LawSubject.AnswerOf<Integer>(var _, var args) ->
                        args.forEach(arg -> subject(arg, anElement));
            }
        }
    }
}
