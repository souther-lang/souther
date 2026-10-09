package souther.compiler.proof;

import souther.compiler.numeric.LinearForm;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.LawSubject;

import java.util.LinkedHashSet;
import java.util.Set;
import java.util.function.Consumer;

/** The values a statement is about, and the ones inside them. */
final class Collect {

    private Collect() {}

    /** Every value {@code holds} names, and every value each of those is made of. */
    static Set<Value> values(LawProposition<Value> holds) {
        Set<Value> out = new LinkedHashSet<>();
        visit(holds, out::add);
        return out;
    }

    /** The values that stand as what an operation, a closure or a sameness is handed — the ones a
     *  statement holding of every value is worth asking of. */
    static Set<Value> handed(LawProposition<Value> holds) {
        Set<Value> out = new LinkedHashSet<>();
        visit(holds, value -> {
            switch (value) {
                case Value.Made(var _, var args) -> out.addAll(args);
                case Value.AppliedTo(var _, var args) -> out.addAll(args);
                default -> { }
            }
        });
        sameness(holds, out);
        return out;
    }

    /** The values {@code holds} asks whether another is the same as, leaving out the element a
     *  statement about some element of a container is about — which stands for each of them and
     *  is no one value. */
    static Set<Value> alike(LawProposition<Value> holds) {
        Set<Value> all = new LinkedHashSet<>();
        sameness(holds, all);
        Set<Value> out = new LinkedHashSet<>();
        all.forEach(value -> {
            Set<Value> inside = new LinkedHashSet<>();
            visit(value, inside::add);
            if (inside.stream().noneMatch(Value.ElementOf.class::isInstance)) {
                out.add(value);
            }
        });
        return out;
    }

    private static void sameness(LawProposition<Value> holds, Set<Value> out) {
        switch (holds) {
            case LawProposition.All<Value>(var parts) -> parts.forEach(part -> sameness(part, out));
            case LawProposition.Any<Value>(var parts) -> parts.forEach(part -> sameness(part, out));
            case LawProposition.SomeElement<Value>(var _, var ofTheElement, var _) ->
                    sameness(ofTheElement, out);
            case LawProposition.Same<Value>(LawSubject<Value> one, LawSubject<Value> other,
                                            var _) -> {
                if (one instanceof LawSubject.Argument<Value>(Value a)) {
                    out.add(a);
                }
                if (other instanceof LawSubject.Argument<Value>(Value b)) {
                    out.add(b);
                }
            }
            case LawProposition.Always<Value> _, LawProposition.Observed<Value> _,
                 LawProposition.Compared<Value> _ -> { }
        }
    }

    /** Every argument word {@code statement} names, wherever it names one. */
    static <A> void slots(LawProposition<A> statement, Consumer<A> each) {
        switch (statement) {
            case LawProposition.Always<A> _ -> { }
            case LawProposition.All<A>(var parts) -> parts.forEach(part -> slots(part, each));
            case LawProposition.Any<A>(var parts) -> parts.forEach(part -> slots(part, each));
            case LawProposition.Observed<A>(LawSubject<A> of, var _) -> slots(of, each);
            case LawProposition.Compared<A>(LinearForm<LawNumber<A>> form, var _) ->
                    form.coefs().keySet().forEach(number -> {
                        switch (number) {
                            case LawNumber.AnArgument<A>(A at) -> each.accept(at);
                            case LawNumber.SizeOf<A>(LawSubject<A> of) -> slots(of, each);
                            case LawNumber.HowManyMeet<A>(A container, var ofTheElement) -> {
                                each.accept(container);
                                slots(ofTheElement, each);
                            }
                        }
                    });
            case LawProposition.SomeElement<A>(A container, var ofTheElement, var _) -> {
                each.accept(container);
                slots(ofTheElement, each);
            }
            case LawProposition.Same<A>(LawSubject<A> one, LawSubject<A> other, var _) -> {
                slots(one, each);
                slots(other, each);
            }
        }
    }

    private static <A> void slots(LawSubject<A> subject, Consumer<A> each) {
        switch (subject) {
            case LawSubject.Argument<A>(A at) -> each.accept(at);
            case LawSubject.ElementOf<A>(A at) -> each.accept(at);
            case LawSubject.KeyOf<A>(A at) -> each.accept(at);
            case LawSubject.WhatTheClosureAnswers<A>(A at) -> each.accept(at);
            case LawSubject.AnswerOf<A>(var _, var args) -> args.forEach(arg -> slots(arg, each));
        }
    }

    private static void visit(LawProposition<Value> holds, Consumer<Value> each) {
        switch (holds) {
            case LawProposition.Always<Value> _ -> { }
            case LawProposition.All<Value>(var parts) -> parts.forEach(part -> visit(part, each));
            case LawProposition.Any<Value>(var parts) -> parts.forEach(part -> visit(part, each));
            case LawProposition.Observed<Value>(LawSubject<Value> of, var _) -> visit(of, each);
            case LawProposition.Compared<Value>(LinearForm<LawNumber<Value>> form, var _) ->
                    form.coefs().keySet().forEach(number -> visit(number, each));
            case LawProposition.SomeElement<Value>(Value container, var ofTheElement, var _) -> {
                visit(container, each);
                visit(ofTheElement, each);
            }
            case LawProposition.Same<Value>(LawSubject<Value> one, LawSubject<Value> other,
                                            var _) -> {
                visit(one, each);
                visit(other, each);
            }
        }
    }

    private static void visit(LawNumber<Value> number, Consumer<Value> each) {
        switch (number) {
            case LawNumber.AnArgument<Value>(Value value) -> visit(value, each);
            case LawNumber.SizeOf<Value>(LawSubject<Value> of) -> visit(of, each);
            case LawNumber.HowManyMeet<Value>(Value container, var ofTheElement) -> {
                visit(container, each);
                visit(ofTheElement, each);
            }
        }
    }

    private static void visit(LawSubject<Value> subject, Consumer<Value> each) {
        switch (subject) {
            case LawSubject.Argument<Value>(Value value) -> visit(value, each);
            case LawSubject.ElementOf<Value>(Value value) -> visit(value, each);
            case LawSubject.KeyOf<Value>(Value value) -> visit(value, each);
            case LawSubject.WhatTheClosureAnswers<Value>(Value value) -> visit(value, each);
            case LawSubject.AnswerOf<Value>(var _, var args) -> args.forEach(arg -> visit(arg, each));
        }
    }

    private static void visit(Value value, Consumer<Value> each) {
        each.accept(value);
        switch (value) {
            case Value.Made(var _, var args) -> args.forEach(arg -> visit(arg, each));
            case Value.Listed(var elements) -> elements.forEach(e -> visit(e, each));
            case Value.Tupled(var elements) -> elements.forEach(e -> visit(e, each));
            case Value.Component(Value tuple, var _) -> visit(tuple, each);
            case Value.AppliedTo(Value function, var args) -> {
                visit(function, each);
                args.forEach(arg -> visit(arg, each));
            }
            case Value.Statement(LawProposition<Value> holds) -> visit(holds, each);
            case Value.Arithmetic(var _, Value left, Value right) -> {
                visit(left, each);
                visit(right, each);
            }
            case Value.Joined(Value left, Value right) -> {
                visit(left, each);
                visit(right, each);
            }
            case Value.ElementOf(Value container) -> visit(container, each);
            case Value.KeyOf(Value element) -> visit(element, each);
            case Value.PayloadOf(Value option) -> visit(option, each);
            case Value.OneMore(Value walked, Value next) -> {
                visit(walked, each);
                visit(next, each);
            }
            case Value.AsEntries(Value entries) -> visit(entries, each);
            case Value.Argument _, Value.Fresh _, Value.Whole _, Value.Decimal _, Value.Truth _,
                 Value.Lambda _, Value.NothingYet _ -> { }
        }
    }
}
