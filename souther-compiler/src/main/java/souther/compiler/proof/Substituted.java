package souther.compiler.proof;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.LawSubject;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * A statement, a number or a value with one value put wherever another stands.
 *
 * <p>What two values being one licenses: whatever is true of something made of the first is true
 * of the same thing made of the second. A closure written in a body is left as it is — what it was
 * closed over is the body's, and nothing a statement says of a value reaches inside one.
 */
final class Substituted {

    private Substituted() {}

    /** {@code value} with {@code to} wherever {@code from} stands in it. */
    static Value value(Value value, Value from, Value to) {
        if (value.equals(from)) {
            return to;
        }
        return switch (value) {
            case Value.Made(var operation, var args) ->
                    new Value.Made(operation, values(args, from, to));
            case Value.Listed(var elements) -> new Value.Listed(values(elements, from, to));
            case Value.Tupled(var elements) -> new Value.Tupled(values(elements, from, to));
            case Value.Component(Value tuple, int index) ->
                    Reading.componentOf(value(tuple, from, to), index);
            case Value.AppliedTo(Value function, var args) ->
                    new Value.AppliedTo(value(function, from, to), values(args, from, to));
            case Value.Statement(LawProposition<Value> holds) ->
                    new Value.Statement(proposition(holds, from, to));
            case Value.Arithmetic(var op, Value left, Value right) ->
                    new Value.Arithmetic(op, value(left, from, to), value(right, from, to));
            case Value.Joined(Value left, Value right) ->
                    new Value.Joined(value(left, from, to), value(right, from, to));
            case Value.ElementOf(Value container) -> new Value.ElementOf(value(container, from, to));
            case Value.KeyOf(Value element) -> new Value.KeyOf(value(element, from, to));
            case Value.PayloadOf(Value option) -> new Value.PayloadOf(value(option, from, to));
            case Value.OneMore(Value walked, Value next) ->
                    new Value.OneMore(value(walked, from, to), value(next, from, to));
            case Value.AsEntries(Value entries) -> new Value.AsEntries(value(entries, from, to));
            case Value.Argument _, Value.Fresh _, Value.Whole _, Value.Decimal _, Value.Truth _,
                 Value.Lambda _, Value.NothingYet _ -> value;
        };
    }

    private static List<Value> values(List<Value> values, Value from, Value to) {
        return values.stream().map(each -> value(each, from, to)).toList();
    }

    /** {@code holds} with {@code to} wherever {@code from} stands in it. */
    static LawProposition<Value> proposition(LawProposition<Value> holds, Value from, Value to) {
        return switch (holds) {
            case LawProposition.Always<Value> always -> always;
            case LawProposition.All<Value>(var parts) -> new LawProposition.All<>(
                    parts.stream().map(part -> proposition(part, from, to)).toList());
            case LawProposition.Any<Value>(var parts) -> new LawProposition.Any<>(
                    parts.stream().map(part -> proposition(part, from, to)).toList());
            case LawProposition.Observed<Value>(var of, var side) ->
                    new LawProposition.Observed<>(subject(of, from, to), side);
            case LawProposition.Compared<Value>(var form, var states) ->
                    new LawProposition.Compared<>(form(form, from, to), states);
            case LawProposition.SomeElement<Value>(Value container, var ofTheElement,
                                                   boolean some) ->
                    new LawProposition.SomeElement<>(value(container, from, to),
                            proposition(ofTheElement, from, to), some);
            case LawProposition.Same<Value>(var one, var other, boolean alike) ->
                    new LawProposition.Same<>(subject(one, from, to), subject(other, from, to),
                            alike);
        };
    }

    /** {@code number} with {@code to} wherever {@code from} stands in it. */
    static LawNumber<Value> number(LawNumber<Value> number, Value from, Value to) {
        return switch (number) {
            case LawNumber.AnArgument<Value>(Value value) ->
                    new LawNumber.AnArgument<>(value(value, from, to));
            case LawNumber.SizeOf<Value>(var of) -> new LawNumber.SizeOf<>(subject(of, from, to));
            case LawNumber.HowManyMeet<Value>(Value container, var ofTheElement) ->
                    new LawNumber.HowManyMeet<>(value(container, from, to),
                            proposition(ofTheElement, from, to));
        };
    }

    private static LinearForm<LawNumber<Value>> form(LinearForm<LawNumber<Value>> form,
                                                     Value from, Value to) {
        LinearForm<LawNumber<Value>> out = LinearForm.constant(form.constant());
        for (Map.Entry<LawNumber<Value>, ExactRatio> term : form.coefs().entrySet()) {
            Map<LawNumber<Value>, ExactRatio> one = new LinkedHashMap<>();
            one.put(number(term.getKey(), from, to), term.getValue());
            out = Props.plus(out, new LinearForm<>(ExactRatio.ZERO, one));
        }
        return out;
    }

    private static LawSubject<Value> subject(LawSubject<Value> subject, Value from, Value to) {
        return switch (subject) {
            case LawSubject.Argument<Value>(Value value) ->
                    new LawSubject.Argument<>(value(value, from, to));
            case LawSubject.ElementOf<Value>(Value value) ->
                    new LawSubject.ElementOf<>(value(value, from, to));
            case LawSubject.KeyOf<Value>(Value value) ->
                    new LawSubject.KeyOf<>(value(value, from, to));
            case LawSubject.WhatTheClosureAnswers<Value>(Value value) ->
                    new LawSubject.WhatTheClosureAnswers<>(value(value, from, to));
            case LawSubject.AnswerOf<Value>(var operation, var args) -> new LawSubject.AnswerOf<>(
                    operation, args.stream().map(arg -> subject(arg, from, to)).toList());
        };
    }
}
