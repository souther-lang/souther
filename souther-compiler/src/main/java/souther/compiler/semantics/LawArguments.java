package souther.compiler.semantics;

import java.util.LinkedHashSet;
import java.util.Set;

/**
 * Which arguments of an operation a number, a subject or a statement of its law names.
 *
 * <p>Asked where a reading of a law is held to the call it was read at: a part of a law reads
 * exactly the arguments it names, and a reading of it that has them standing anywhere but where the
 * call has them is not a reading of that call.
 */
public final class LawArguments {

    private LawArguments() {
    }

    /** Every argument {@code subject} names, down to those of the answers it holds. */
    public static <A> Set<A> named(LawSubject<A> subject) {
        Set<A> out = new LinkedHashSet<>();
        into(subject, out);
        return out;
    }

    /** Every argument {@code number} names, down to those of the statements it counts by. */
    public static <A> Set<A> named(LawNumber<A> number) {
        Set<A> out = new LinkedHashSet<>();
        into(number, out);
        return out;
    }

    /** Every argument {@code statement} names, in the parts it joins and the elements it is about. */
    public static <A> Set<A> named(LawProposition<A> statement) {
        Set<A> out = new LinkedHashSet<>();
        into(statement, out);
        return out;
    }

    private static <A> void into(LawSubject<A> subject, Set<A> out) {
        switch (subject) {
            case LawSubject.Argument<A>(A argument) -> out.add(argument);
            case LawSubject.ElementOf<A>(A container) -> out.add(container);
            case LawSubject.WhatTheClosureAnswers<A>(A closure) -> out.add(closure);
            case LawSubject.KeyOf<A>(A container) -> out.add(container);
            case LawSubject.AnswerOf<A>(var _, var args) -> args.forEach(each -> into(each, out));
        }
    }

    private static <A> void into(LawNumber<A> number, Set<A> out) {
        switch (number) {
            case LawNumber.AnArgument<A>(A argument) -> out.add(argument);
            case LawNumber.SizeOf<A>(LawSubject<A> of) -> into(of, out);
            case LawNumber.HowManyMeet<A>(A container, LawProposition<A> ofTheElement) -> {
                out.add(container);
                into(ofTheElement, out);
            }
            case LawNumber.HowManyDifferent<A>(A container, LawSubject<A> ofTheElement) -> {
                out.add(container);
                into(ofTheElement, out);
            }
            case LawNumber.SumOver<A>(A container, LawNumber<A> ofTheElement) -> {
                out.add(container);
                into(ofTheElement, out);
            }
        }
    }

    private static <A> void into(LawProposition<A> statement, Set<A> out) {
        switch (statement) {
            case LawProposition.Always<A> _ -> { }
            case LawProposition.All<A>(var parts) -> parts.forEach(each -> into(each, out));
            case LawProposition.Any<A>(var parts) -> parts.forEach(each -> into(each, out));
            case LawProposition.Observed<A>(LawSubject<A> of, var _) -> into(of, out);
            case LawProposition.Compared<A>(var form, var _) ->
                    form.coefs().keySet().forEach(each -> into(each, out));
            case LawProposition.SomeElement<A>(A container, LawProposition<A> ofTheElement,
                                               var _) -> {
                out.add(container);
                into(ofTheElement, out);
            }
            case LawProposition.Same<A>(LawSubject<A> one, LawSubject<A> other, var _) -> {
                into(one, out);
                into(other, out);
            }
        }
    }
}
