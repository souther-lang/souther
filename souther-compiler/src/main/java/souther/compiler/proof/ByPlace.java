package souther.compiler.proof;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.LawSubject;
import souther.compiler.semantics.OperationLaw;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.function.Function;

/**
 * A law with every argument it names read as another word for it: from the declaration's own
 * argument to its place, which is how a proof reads one, and back.
 *
 * <p>Structure and nothing else. Which arguments a law names and where each stands in it are
 * what is kept; what an argument is called is the caller's.
 */
public final class ByPlace {

    private ByPlace() {}

    public static <A, B> OperationLaw<B> law(OperationLaw<A> law, Function<A, B> word) {
        return switch (law) {
            case OperationLaw.Observation<A>(var aspect, LawProposition<A> holds) ->
                    new OperationLaw.Observation<>(aspect, proposition(holds, word));
            case OperationLaw.Size<A>(var cases) -> new OperationLaw.Size<>(cases.stream()
                    .map(each -> new OperationLaw.Size.Case<>(proposition(each.where(), word),
                            form(each.equalTo(), word)))
                    .toList());
        };
    }

    public static <A, B> LawProposition<B> proposition(LawProposition<A> holds, Function<A, B> word) {
        return switch (holds) {
            case LawProposition.Always<A>(boolean always) -> new LawProposition.Always<>(always);
            case LawProposition.All<A>(var parts) -> new LawProposition.All<>(
                    parts.stream().map(part -> proposition(part, word)).toList());
            case LawProposition.Any<A>(var parts) -> new LawProposition.Any<>(
                    parts.stream().map(part -> proposition(part, word)).toList());
            case LawProposition.Observed<A>(LawSubject<A> of, var side) ->
                    new LawProposition.Observed<>(subject(of, word), side);
            case LawProposition.Compared<A>(LinearForm<LawNumber<A>> form, var states) ->
                    new LawProposition.Compared<>(form(form, word), states);
            case LawProposition.SomeElement<A>(A container, LawProposition<A> ofTheElement,
                                               boolean some) ->
                    new LawProposition.SomeElement<>(word.apply(container),
                            proposition(ofTheElement, word), some);
            case LawProposition.Same<A>(LawSubject<A> one, LawSubject<A> other, boolean alike) ->
                    new LawProposition.Same<>(subject(one, word), subject(other, word), alike);
        };
    }

    public static <A, B> LinearForm<LawNumber<B>> form(LinearForm<LawNumber<A>> form,
                                                       Function<A, B> word) {
        Map<LawNumber<B>, ExactRatio> coefs = new LinkedHashMap<>();
        form.coefs().forEach((number, coef) -> {
            if (coefs.put(number(number, word), coef) != null) {
                throw new IllegalArgumentException("two numbers of a law are one number in the"
                        + " other word for its arguments: " + form);
            }
        });
        return new LinearForm<>(form.constant(), coefs);
    }

    private static <A, B> LawNumber<B> number(LawNumber<A> number, Function<A, B> word) {
        return switch (number) {
            case LawNumber.AnArgument<A>(A argument) -> new LawNumber.AnArgument<>(
                    word.apply(argument));
            case LawNumber.SizeOf<A>(LawSubject<A> of) -> new LawNumber.SizeOf<>(subject(of, word));
            case LawNumber.HowManyMeet<A>(A container, LawProposition<A> ofTheElement) ->
                    new LawNumber.HowManyMeet<>(word.apply(container),
                            proposition(ofTheElement, word));
        };
    }

    private static <A, B> LawSubject<B> subject(LawSubject<A> subject, Function<A, B> word) {
        return switch (subject) {
            case LawSubject.Argument<A>(A argument) -> new LawSubject.Argument<>(word.apply(argument));
            case LawSubject.ElementOf<A>(A container) ->
                    new LawSubject.ElementOf<>(word.apply(container));
            case LawSubject.WhatTheClosureAnswers<A>(A closure) ->
                    new LawSubject.WhatTheClosureAnswers<>(word.apply(closure));
            case LawSubject.KeyOf<A>(A container) -> new LawSubject.KeyOf<>(word.apply(container));
            case LawSubject.AnswerOf<A>(var operation, var args) -> new LawSubject.AnswerOf<>(
                    operation, args.stream().map(arg -> subject(arg, word)).toList());
        };
    }
}
