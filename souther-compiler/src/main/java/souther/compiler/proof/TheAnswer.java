package souther.compiler.proof;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.LawSubject;
import souther.compiler.types.ValueName;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * A statement about an operation's answer with that answer named as itself.
 *
 * <p>Where the operation is called, a statement about what it answers names the answer as the
 * operation handed its arguments, and that is how it is written. Proved against the body, the
 * answer is what the body comes to and not a call of the operation, so the operation handed its own
 * arguments, in order, is read as {@link Slot.Answer} — and nothing else is.
 */
final class TheAnswer {

    private TheAnswer() {}

    static LawProposition<Slot> named(LawProposition<Slot> holds,
                                      ValueName.Stdlib.Operation operation, int arity) {
        return new TheAnswer.Naming(operation, arity).proposition(holds);
    }

    private record Naming(ValueName.Stdlib.Operation operation, int arity) {

        LawProposition<Slot> proposition(LawProposition<Slot> holds) {
            return switch (holds) {
                case LawProposition.Always<Slot> always -> always;
                case LawProposition.All<Slot>(var parts) ->
                        new LawProposition.All<>(parts.stream().map(this::proposition).toList());
                case LawProposition.Any<Slot>(var parts) ->
                        new LawProposition.Any<>(parts.stream().map(this::proposition).toList());
                case LawProposition.Observed<Slot>(var of, var side) ->
                        new LawProposition.Observed<>(subject(of), side);
                case LawProposition.Compared<Slot>(var form, var states) ->
                        new LawProposition.Compared<>(form(form), states);
                case LawProposition.SomeElement<Slot>(Slot container, var ofTheElement,
                                                      boolean some) ->
                        new LawProposition.SomeElement<>(container, proposition(ofTheElement),
                                some);
                case LawProposition.Same<Slot>(var one, var other, boolean alike) ->
                        new LawProposition.Same<>(subject(one), subject(other), alike);
            };
        }

        private LinearForm<LawNumber<Slot>> form(LinearForm<LawNumber<Slot>> form) {
            Map<LawNumber<Slot>, ExactRatio> coefs = new LinkedHashMap<>();
            form.coefs().forEach((number, coef) -> {
                if (coefs.put(number(number), coef) != null) {
                    throw new IllegalArgumentException("two numbers of a statement are one number"
                            + " once its answer is named as itself: " + form);
                }
            });
            return new LinearForm<>(form.constant(), coefs);
        }

        private LawNumber<Slot> number(LawNumber<Slot> number) {
            return switch (number) {
                case LawNumber.AnArgument<Slot> argument -> argument;
                case LawNumber.SizeOf<Slot>(var of) -> new LawNumber.SizeOf<>(subject(of));
                case LawNumber.HowManyMeet<Slot>(Slot container, var ofTheElement) ->
                        new LawNumber.HowManyMeet<>(container, proposition(ofTheElement));
                case LawNumber.HowManyDifferent<Slot>(Slot container, var ofTheElement) ->
                        new LawNumber.HowManyDifferent<>(container, subject(ofTheElement));
                case LawNumber.SumOver<Slot>(Slot container, var ofTheElement) ->
                        new LawNumber.SumOver<>(container, number(ofTheElement));
            };
        }

        private LawSubject<Slot> subject(LawSubject<Slot> subject) {
            if (!(subject instanceof LawSubject.AnswerOf<Slot>(var answering,
                    List<LawSubject<Slot>> args))) {
                return subject;
            }
            if (answering.equals(operation) && ownArguments(args)) {
                return new LawSubject.Argument<>(new Slot.Answer());
            }
            return new LawSubject.AnswerOf<>(answering, args.stream().map(this::subject).toList());
        }

        private boolean ownArguments(List<LawSubject<Slot>> args) {
            if (args.size() != arity) {
                return false;
            }
            for (int at = 0; at < arity; at++) {
                if (!(args.get(at) instanceof LawSubject.Argument<Slot>(Slot.Place(int position)))
                        || position != at) {
                    return false;
                }
            }
            return true;
        }
    }
}
